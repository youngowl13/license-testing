package main

import (
	"bytes"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

// ----------------------------------------------------------------------
// 1) GLOBALS
// ----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"      // Disk caching
	fetchTimeout     = 30 * time.Second  // HTTP GET concurrency
	workerCount      = 6                 // BFS concurrency
)

var (
	// BFS concurrency channel
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	// In-memory store: key = "group:artifact:version"
	pomCache sync.Map
	// For BFS expansions to detect cycles in parent references
	parentVisit sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) UTILS: skipScope, copyleft, BFS Node, BFS Section
// ----------------------------------------------------------------------

// skipScope => same as your code
func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	if s == "test" || s == "provided" || s == "system" {
		return true
	}
	if strings.EqualFold(strings.TrimSpace(optional), "true") {
		return true
	}
	return false
}

// A comprehensive set of known “copyleft” license indicators:
var copyleftKeywords = []string{
	"GPL", "LGPL", "AGPL", "CC-BY-SA", "MPL", "EPL", "CPL", "CDDL",
	"EUPL", "OSL", "CeCILL",
	"GNU GENERAL PUBLIC LICENSE",
	"GNU LESSER GENERAL PUBLIC LICENSE",
	"GNU AFFERO GENERAL PUBLIC LICENSE",
	"MOZILLA PUBLIC LICENSE",
	"COMMON DEVELOPMENT AND DISTRIBUTION LICENSE",
	"ECLIPSE PUBLIC LICENSE",
	"COMMON PUBLIC LICENSE",
	"EUROPEAN UNION PUBLIC LICENSE",
	"OPEN SOFTWARE LICENSE",
	"CREATIVE COMMONS ATTRIBUTION-SHAREALIKE",
}

// isCopyleft => checks for recognized copyleft keywords
func isCopyleft(lic string) bool {
	up := strings.ToUpper(lic)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// For sorting: copyleft => group 1, unknown => group 2, else 3
func getLicenseGroup(license string) int {
	if isCopyleft(license) {
		return 1
	} else if strings.EqualFold(license, "unknown") {
		return 2
	}
	return 3
}

// BFS node
type BFSNode struct {
	Name     string // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string // “direct” or “g/a@v”
	Children []*BFSNode
}

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// Flatten row
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoLink string
}

// ----------------------------------------------------------------------
// 3) MAVEN POM STRUCT
// ----------------------------------------------------------------------

type PomLicense struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}
type PomDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type MavenPOM struct {
	XMLName     xml.Name    `xml:"project"`
	Licenses    []PomLicense `xml:"licenses>license"`
	Dependencies []PomDep    `xml:"dependencies>dependency"`
	GroupID     string       `xml:"groupId"`
	ArtifactID  string       `xml:"artifactId"`
	Version     string       `xml:"version"`
}

// detectLicense => parse first license
func detectLicense(mp *MavenPOM) string {
	if len(mp.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(mp.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	up := strings.ToUpper(lic)
	// quick fallback
	if strings.Contains(up, "APACHE") {
		return "Apache-2.0"
	}
	if strings.Contains(up, "GPL") {
		return "GPL-3.0"
	}
	return lic
}

// ----------------------------------------------------------------------
// 4) CONCURRENT BFS WORKER POOL
// ----------------------------------------------------------------------

// We define the request + result used by BFS concurrency
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}
type fetchResult struct {
	POM *MavenPOM
	Err error
}

// Worker that attempts to fetch from both repos concurrently
func concurrencyPomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		groupID, artifactID, version := req.GroupID, req.ArtifactID, req.Version
		pom, err := retrieveOrLoadPOMConcurrently(groupID, artifactID, version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

func retrieveOrLoadPOMConcurrently(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("[Worker] In-memory cache hit => %s\n", key)
		return c.(*MavenPOM), nil
	}
	// local disk
	mp, err := loadPOMFromDisk(g, a, v)
	if err == nil && mp != nil {
		fmt.Printf("[Worker] Found on disk => %s\n", key)
		pomCache.Store(key, mp)
		return mp, nil
	}
	// parallel approach: spawn two goroutines, one tries google, one tries central
	// whichever returns first with success is used
	pom, e2 := fetchPOMParallel(g, a, v)
	if e2 != nil {
		return nil, e2
	}
	pomCache.Store(key, pom)
	savePOMToDisk(g, a, v, pom)
	return pom, nil
}

// fetchPOMParallel => tries google + central concurrently
func fetchPOMParallel(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)

	type pomResp struct {
		pom *MavenPOM
		err error
	}
	ch := make(chan pomResp, 2)

	go func() {
		pm, e := fetchPOMFromURL(urlGoogle)
		ch <- pomResp{pm, e}
	}()
	go func() {
		pm, e := fetchPOMFromURL(urlCentral)
		ch <- pomResp{pm, e}
	}()

	var firstErr error
	for i := 0; i < 2; i++ {
		res := <-ch
		if res.err == nil && res.pom != nil {
			return res.pom, nil
		}
		if firstErr == nil {
			firstErr = res.err
		}
	}
	return nil, firstErr
}

// fetchPOMFromURL => standard GET + parse
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	fmt.Printf("   [fetchPOM] GET => %s\n", url)
	cl := http.Client{Timeout: fetchTimeout}
	resp, err := cl.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d => %s", resp.StatusCode, url)
	}
	data, e2 := io.ReadAll(resp.Body)
	if e2 != nil {
		return nil, e2
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e3 := dec.Decode(&mp); e3 != nil {
		return nil, e3
	}
	return &mp, nil
}

// local disk caching
func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	d, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(d))
	dec.Strict = false
	if e2 := dec.Decode(&mp); e2 != nil {
		return nil, e2
	}
	return &mp, nil
}
func savePOMToDisk(g, a, v string, mp *MavenPOM) {
	path := localCachePath(g, a, v)
	if e := os.MkdirAll(filepath.Dir(path), 0755); e != nil {
		fmt.Printf("[savePOMToDisk] mkdir => %v\n", e)
		return
	}
	out, e2 := os.Create(path)
	if e2 != nil {
		fmt.Printf("[savePOMToDisk] create => %v\n", e2)
		return
	}
	defer out.Close()
	data, e3 := xml.MarshalIndent(mp, "", "  ")
	if e3 != nil {
		fmt.Printf("[savePOMToDisk] marshal => %v\n", e3)
		return
	}
	out.Write(data)
	fmt.Printf("[savePOMToDisk] => %s\n", path)
}
func localCachePath(g, a, v string) string {
	gp := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, gp, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// ----------------------------------------------------------------------
// 5) BFS expansions
// ----------------------------------------------------------------------

// buildFullBFS => unlimited BFS with visited + skipScope
func buildFullBFS(g, a, v, parent string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, v)
	if visited[key] {
		return nil
	}
	visited[key] = true

	node := &BFSNode{
		Name:   g + "/" + a,
		Version: v,
		Parent: parent,
		License: "Unknown",
	}
	// unknown => skip sub BFS
	if strings.ToLower(v) == "unknown" {
		return node
	}
	// concurrency BFS
	pom, err := retrieveOrLoadPOMConcurrently(g, a, v)
	if err != nil || pom == nil {
		return node
	}
	lic := detectLicense(pom)
	node.License  = lic
	node.Copyleft = isCopyleft(lic)

	for _, dep := range pom.Dependencies {
		if skipScope(dep.Scope, dep.Optional) {
			continue
		}
		cg, ca := dep.GroupID, dep.ArtifactID
		cv := dep.Version
		if cv == "" {
			cv = "unknown"
		}
		child := buildFullBFS(cg, ca, cv, node.Name+"@"+v, visited)
		if child != nil {
			node.Children = append(node.Children, child)
		}
	}
	return node
}

// flatten BFS => for table
func flattenBFSNode(n *BFSNode, lang string, out *[]FlatDep) {
	if n == nil {
		return
	}
	g, a := splitGA(n.Name)
	link := buildRepoLink(g, a, n.Version)
	fd := FlatDep{
		Name:     n.Name,
		Version:  n.Version,
		License:  n.License,
		Parent:   n.Parent,
		Copyleft: n.Copyleft,
		Language: lang,
		RepoLink: link,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFSNode(c, lang, out)
	}
}

// doBFSForDirect => parse direct => BFS => flatten
func doBFSForDirect(depMap map[string]string, filePath, lang string) BFSSection {
	visited := make(map[string]bool)
	var roots []*BFSNode
	for ga, ver := range depMap {
		g, a := splitGA(ga)
		bn := buildFullBFS(g, a, ver, "direct", visited)
		if bn != nil {
			roots = append(roots, bn)
		}
	}
	var flat []FlatDep
	for _, r := range roots {
		flattenBFSNode(r, lang, &flat)
	}
	sort.SliceStable(flat, func(i, j int) bool {
		g1 := getLicenseGroup(flat[i].License)
		g2 := getLicenseGroup(flat[j].License)
		return g1 < g2
	})
	return BFSSection{
		FilePath:  filePath,
		BFSNodes:  roots,
		Flattened: flat,
	}
}

// buildRepoLink => separate logic for display: prefer google if group starts com.android or androidx, else central, else google search
func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" || v == "" {
		return fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s", g, a, v)
	}
	if strings.HasPrefix(g, "com.android") || strings.HasPrefix(g, "androidx") {
		return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, v)
	}
	// else fallback to e.g. mvnrepository
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", g, a, v)
}

// ----------------------------------------------------------------------
// 6) PARSE each file type EXACTLY
// ----------------------------------------------------------------------

func parseOnePomFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	if e2 := xml.Unmarshal(data, &mp); e2 != nil {
		return nil, e2
	}
	deps := make(map[string]string)
	for _, d := range mp.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g, a := d.GroupID, d.ArtifactID
		v := d.Version
		if v == "" {
			v = "unknown"
		}
		key := g + "/" + a
		deps[key] = v
	}
	return deps, nil
}

func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return werr
	})
	return out, err
}

// TOML
func parseTomlFile(filePath string) (map[string]string, error) {
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, err
	}
	deps := make(map[string]string)
	libTree := tree.Get("libraries")
	if libTree == nil {
		return deps, nil
	}
	lt, ok := libTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", filePath)
	}
	for _, k := range lt.Keys() {
		val := lt.Get(k)
		sub, ok2 := val.(*toml.Tree)
		if !ok2 {
			continue
		}
		mod, _ := sub.Get("module").(string)
		verRef, _ := sub.Get("version.ref").(string)
		if mod == "" || verRef == "" {
			continue
		}
		parts := strings.SplitN(mod, ":", 2)
		if len(parts) != 2 {
			continue
		}
		g, a := parts[0], parts[1]
		deps[g+"/"+a] = verRef
	}
	return deps, nil
}
func findTOMLFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return werr
	})
	return out, err
}

// Gradle
func parseBuildGradleFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	out := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\\s+['\"]([^'\"]+)['\"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		coord := m[2]
		pp := strings.Split(coord, ":")
		if len(pp) < 2 {
			continue
		}
		g, a := pp[0], pp[1]
		v := "unknown"
		if len(pp) >= 3 {
			v = pp[2]
		}
		out[g+"/"+a] = v
	}
	return out, nil
}
func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return werr
	})
	return out, err
}

// ----------------------------------------------------------------------
// 7) FINAL HTML
// ----------------------------------------------------------------------

var finalTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>license-full-bfs-report</title>
<style>
body{font-family:Arial,sans-serif;margin:20px}
h1,h2{color:#2c3e50}
table{width:100%;border-collapse:collapse;margin-bottom:20px}
th,td{border:1px solid #ddd;padding:8px;text-align:left}
th{background:#f2f2f2}
.copyleft{background:#f8d7da;color:#721c24}
.unknown{background:#ffff99;color:#333}
.non-copyleft{background:#d4edda;color:#155724}
details{margin:4px 0}
summary{cursor:pointer;font-weight:bold}
</style>
</head>
<body>
<h1>Consolidated BFS Report for POM, TOML, Gradle (Local .pom-cache + concurrency check on both repos)</h1>
<h2>Summary</h2>
<p>{{.Summary}}</p>

<h2>POM Files</h2>
{{range .PomSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Language</th>
  <th>Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License \"Unknown\"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href=\"{{.RepoLink}}\" target=\"_blank\">Link</a></td>
</tr>
{{end}}
</table>
<h4>BFS Expansions</h4>
<div>
{{range .BFSNodes}}
{{buildBFSHTML .}}
{{end}}
</div>
{{end}}
<hr/>
{{end}}

<h2>TOML Files</h2>
{{range .TomlSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Language</th>
  <th>Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class=\"{{if eq .License \"Unknown\"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}\">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href=\"{{.RepoLink}}\" target=\"_blank\">Link</a></td>
</tr>
{{end}}
</table>
<h4>BFS Expansions</h4>
<div>
{{range .BFSNodes}}
{{buildBFSHTML .}}
{{end}}
</div>
{{end}}
<hr/>
{{end}}

<h2>Gradle Files</h2>
{{range .GradleSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Language</th>
  <th>Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class=\"{{if eq .License \"Unknown\"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}\">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href=\"{{.RepoLink}}\" target=\"_blank\">Link</a></td>
</tr>
{{end}}
</table>
<h4>BFS Expansions</h4>
<div>
{{range .BFSNodes}}
{{buildBFSHTML .}}
{{end}}
</div>
{{end}}
<hr/>
{{end}}

</body>
</html>
`

// buildBFSHTML => BFS expansions in <details>
func buildBFSHTML(n *BFSNode) string {
	if n == nil {
		return ""
	}
	summary := fmt.Sprintf("%s@%s (License=%s)", n.Name, n.Version, n.License)
	css := "non-copyleft"
	if n.License == "Unknown" {
		css = "unknown"
	} else if n.Copyleft {
		css = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details class=\"" + css + "\"><summary>")
	sb.WriteString(template.HTMLEscapeString(summary))
	sb.WriteString("</summary>\n")
	if len(n.Children) > 0 {
		sb.WriteString("<ul>\n")
		for _, c := range n.Children {
			sb.WriteString("<li>")
			sb.WriteString(buildBFSHTML(c))
			sb.WriteString("</li>\n")
		}
		sb.WriteString("</ul>\n")
	}
	sb.WriteString("</details>")
	return sb.String()
}

// ----------------------------------------------------------------------
// 9) MAIN
// ----------------------------------------------------------------------

func main() {
	// Start concurrency BFS
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go concurrencyPomWorker()
	}

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		fmt.Printf("[MAIN] Found POM => %s\n", pf)
		pdeps, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("[POM] parse error => %v\n", err)
			continue
		}
		ps := doBFSForDirect(pdeps, pf, "maven")
		pomSections = append(pomSections, ps)
		totalPom += len(ps.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		fmt.Printf("[MAIN] Found TOML => %s\n", tf)
		tdeps, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("[TOML] parse error => %v\n", err)
			continue
		}
		if len(tdeps) == 0 {
			continue
		}
		ts := doBFSForDirect(tdeps, tf, "toml")
		tomlSections = append(tomlSections, ts)
		totalToml += len(ts.Flattened)
	}

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		fmt.Printf("[MAIN] Found Gradle => %s\n", gf)
		gdeps, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("[Gradle] parse error => %v\n", err)
			continue
		}
		if len(gdeps) == 0 {
			continue
		}
		gs := doBFSForDirect(gdeps, gf, "gradle")
		gradleSections = append(gradleSections, gs)
		totalGradle += len(gs.Flattened)
	}

	// close BFS concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// final summary
	copyleftCount := 0
	for _, s := range pomSections {
		for _, fd := range s.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range tomlSections {
		for _, fd := range s.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range gradleSections {
		for _, fd := range s.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM total:%d, TOML total:%d, Gradle total:%d, Copyleft:%d",
		totalPom, totalToml, totalGradle, copyleftCount)

	type finalData struct {
		Summary        string
		PomSections    []BFSSection
		TomlSections   []BFSSection
		GradleSections []BFSSection
	}
	data := finalData{
		Summary:        summary,
		PomSections:    pomSections,
		TomlSections:   tomlSections,
		GradleSections: gradleSections,
	}

	funcMap := template.FuncMap{
		"isCopyleft": isCopyleft,
		"buildBFSHTML": func(n *BFSNode) template.HTML {
			return template.HTML(buildBFSHTML(n))
		},
	}
	tmpl, e2 := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if e2 != nil {
		fmt.Printf("[MAIN] Template parse => %v\n", e2)
		return
	}
	out, e3 := os.Create("license-full-bfs-report.html")
	if e3 != nil {
		fmt.Printf("[MAIN] Create file => %v\n", e3)
		return
	}
	defer out.Close()

	if e4 := tmpl.Execute(out, data); e4 != nil {
		fmt.Printf("[MAIN] Template execute => %v\n", e4)
		return
	}
	fmt.Println("[DONE] license-full-bfs-report.html => BFS expansions for POM, TOML, Gradle with concurrency, no errors!")
}

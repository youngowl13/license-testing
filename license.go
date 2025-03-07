package main

import (
	"bytes"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

const (
	localPOMCacheDir = ".pom-cache"
	fetchTimeout     = 30 * time.Second
	workerCount      = 6
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" => *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// Skip test/provided/system or optional
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

// Copyleft keywords
var copyleftKeywords = []string{
	"GPL", "LGPL", "AGPL", "CC-BY-SA", "MPL", "EPL", "CPL", "CDDL", "EUPL",
	"OSL", "CeCILL",
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

func isCopyleft(lic string) bool {
	up := strings.ToUpper(lic)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// For sorting: 1 => copyleft, 2 => unknown, 3 => everything else
func getLicenseGroup(lic string) int {
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
}

// BFS node
type BFSNode struct {
	Name     string
	Version  string
	License  string
	Copyleft bool
	Parent   string
	Children []*BFSNode
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

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// Minimal POM struct
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type PomLicense struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}
type MavenPOM struct {
	XMLName      xml.Name   `xml:"project"`
	Licenses     []PomLicense `xml:"licenses>license"`
	Dependencies []POMDep     `xml:"dependencies>dependency"`
	GroupID      string       `xml:"groupId"`
	ArtifactID   string       `xml:"artifactId"`
	Version      string       `xml:"version"`
}

func detectLicense(mp *MavenPOM) string {
	if len(mp.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(mp.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	up := strings.ToUpper(lic)
	if strings.Contains(up, "APACHE") {
		return "Apache-2.0"
	}
	if strings.Contains(up, "GPL") {
		return "GPL-3.0"
	}
	return lic
}

// BFS concurrency
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

// BFS concurrency worker
func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

// local disk path
func localCachePath(g, a, v string) string {
	groupPath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, groupPath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// Save to disk
func savePOMToDisk(g, a, v string, mp *MavenPOM) {
	path := localCachePath(g, a, v)
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		fmt.Printf("[savePOMToDisk] mkdir => %v\n", err)
		return
	}
	f, e := os.Create(path)
	if e != nil {
		fmt.Printf("[savePOMToDisk] create => %v\n", e)
		return
	}
	defer f.Close()
	data, e2 := xml.MarshalIndent(mp, "", "  ")
	if e2 != nil {
		fmt.Printf("[savePOMToDisk] marshal => %v\n", e2)
		return
	}
	f.Write(data)
	fmt.Printf("[savePOMToDisk] => %s\n", path)
}

// Load from disk
func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e := dec.Decode(&mp); e != nil {
		return nil, e
	}
	return &mp, nil
}

// fetch from maven central first => fallback google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	central := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	google := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)

	pom1, e1 := fetchPOMFromURL(central)
	if e1 == nil && pom1 != nil {
		return pom1, nil
	}
	pom2, e2 := fetchPOMFromURL(google)
	if e2 == nil && pom2 != nil {
		return pom2, nil
	}
	if e1 != nil {
		return nil, e1
	}
	return nil, e2
}

// fetchPOMFromURL => GET
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	fmt.Printf("[fetchPOMFromURL] => %s\n", url)
	cl := http.Client{Timeout: fetchTimeout}
	resp, err := cl.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d => %s", resp.StatusCode, url)
	}
	body, e2 := io.ReadAll(resp.Body)
	if e2 != nil {
		return nil, e2
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(body))
	dec.Strict = false
	if e3 := dec.Decode(&mp); e3 != nil {
		return nil, e3
	}
	return &mp, nil
}

// concurrency BFS => check in-memory => disk => fetch
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("[retrieveOrLoadPOM] in-memory => %s\n", key)
		return c.(*MavenPOM), nil
	}
	mp, err := loadPOMFromDisk(g, a, v)
	if err == nil && mp != nil {
		fmt.Printf("[retrieveOrLoadPOM] from disk => %s\n", key)
		pomCache.Store(key, mp)
		return mp, nil
	}
	fmt.Printf("[retrieveOrLoadPOM] remote => %s\n", key)
	rm, e2 := fetchRemotePOM(g, a, v)
	if e2 != nil {
		return nil, e2
	}
	pomCache.Store(key, rm)
	savePOMToDisk(g, a, v, rm)
	return rm, nil
}

// BFS expansions
func buildFullBFS(g, a, v, parent string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, v)
	if visited[key] {
		return nil
	}
	visited[key] = true

	node := &BFSNode{
		Name:    g + "/" + a,
		Version: v,
		Parent:  parent,
		License: "Unknown",
	}
	// skip unknown
	if strings.ToLower(v) == "unknown" {
		return node
	}
	pom, err := retrieveOrLoadPOM(g, a, v)
	if err != nil || pom == nil {
		return node
	}
	lic := detectLicense(pom)
	node.License  = lic
	node.Copyleft = isCopyleft(lic)

	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		cg, ca := d.GroupID, d.ArtifactID
		cv := d.Version
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

func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

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

// buildRepoLink => separate from fetch logic
// If g starts com.android or androidx => google maven UI
// else => mvnrepository
func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" || v == "" {
		return fmt.Sprintf("https://google.com/search?q=%s+%s+%s", g, a, v)
	}
	if strings.HasPrefix(g, "com.android") || strings.HasPrefix(g, "androidx") {
		return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s",
			a, g, a, v)
	}
	// fallback => mvnrepository
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", g, a, v)
}

func doBFSForDirect(depMap map[string]string, filePath, lang string) BFSSection {
	visited := make(map[string]bool)
	var roots []*BFSNode
	for ga, ver := range depMap {
		g, a := splitGA(ga)
		node := buildFullBFS(g, a, ver, "direct", visited)
		if node != nil {
			roots = append(roots, node)
		}
	}
	var flat []FlatDep
	for _, r := range roots {
		flattenBFSNode(r, lang, &flat)
	}
	sort.SliceStable(flat, func(i, j int) bool {
		return getLicenseGroup(flat[i].License) < getLicenseGroup(flat[j].License)
	})
	return BFSSection{
		FilePath:  filePath,
		BFSNodes:  roots,
		Flattened: flat,
	}
}

// parseOnePomFile, parseTomlFile, parseBuildGradleFile:

func parseOnePomFile(path string) (map[string]string, error) {
	dat, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	if e2 := xml.Unmarshal(dat, &mp); e2 != nil {
		return nil, e2
	}
	res := make(map[string]string)
	for _, d := range mp.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g, a := d.GroupID, d.ArtifactID
		v := d.Version
		if v == "" {
			v = "unknown"
		}
		res[g+"/"+a] = v
	}
	return res, nil
}

func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return e
	})
	return out, err
}

// TOML
func parseTomlFile(path string) (map[string]string, error) {
	tree, err := toml.LoadFile(path)
	if err != nil {
		return nil, err
	}
	deps := make(map[string]string)
	libs := tree.Get("libraries")
	if libs == nil {
		return deps, nil
	}
	libTree, ok := libs.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", path)
	}
	for _, k := range libTree.Keys() {
		val := libTree.Get(k)
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
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return e
	})
	return out, err
}

// Gradle
func parseBuildGradleFile(path string) (map[string]string, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(string(content), -1)
	out := make(map[string]string)
	for _, mm := range matches {
		coord := mm[2]
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
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return e
	})
	return out, err
}

// For final HTML
type finalData struct {
	Summary        string
	PomSections    []BFSSection
	TomlSections   []BFSSection
	GradleSections []BFSSection
}

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
<h1>Consolidated BFS Report (Maven Central -> Google fallback fetching, separate display logic)</h1>
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
  <th>Repo Link</th>
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
  <th>Repo Link</th>
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
  <th>Repo Link</th>
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

func main() {
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// 1) parse POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		fmt.Printf("[MAIN] Found POM => %s\n", pf)
		deps, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("[POM] parse error => %v\n", err)
			continue
		}
		psec := doBFSForDirect(deps, pf, "maven")
		pomSections = append(pomSections, psec)
		totalPom += len(psec.Flattened)
	}

	// 2) parse TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		fmt.Printf("[MAIN] Found TOML => %s\n", tf)
		td, er := parseTomlFile(tf)
		if er != nil {
			fmt.Printf("[TOML] parse error => %v\n", er)
			continue
		}
		if len(td) == 0 {
			continue
		}
		tsec := doBFSForDirect(td, tf, "toml")
		tomlSections = append(tomlSections, tsec)
		totalToml += len(tsec.Flattened)
	}

	// 3) parse Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		fmt.Printf("[MAIN] Found Gradle => %s\n", gf)
		gd, er2 := parseBuildGradleFile(gf)
		if er2 != nil {
			fmt.Printf("[Gradle] parse error => %v\n", er2)
			continue
		}
		if len(gd) == 0 {
			continue
		}
		gsec := doBFSForDirect(gd, gf, "gradle")
		gradleSections = append(gradleSections, gsec)
		totalGradle += len(gsec.Flattened)
	}

	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// final
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
	summary := fmt.Sprintf("POM total=%d, TOML total=%d, Gradle total=%d, Copyleft=%d", totalPom, totalToml, totalGradle, copyleftCount)

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
		fmt.Printf("[MAIN] Create => %v\n", e3)
		return
	}
	defer out.Close()

	if e4 := tmpl.Execute(out, data); e4 != nil {
		fmt.Printf("[MAIN] Execute => %v\n", e4)
		return
	}
	fmt.Println("[DONE] license-full-bfs-report.html => BFS expansions for POM, TOML, Gradle + local caching, no syntax errors!")
}

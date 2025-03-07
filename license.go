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

// ----------------------------------------------------------------------
// 1) GLOBALS & CONSTANTS
// ----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"
	pomWorkerCount   = 10
	fetchTimeout     = 30 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit  sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) DATA STRUCTS FROM YOUR 3 FILES
// ----------------------------------------------------------------------

// spdxLicenseMap, skipScope, isCopyleft, etc. from your codes
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":          {Name: "MIT License", Copyleft: false},
	"Apache-2.0":   {Name: "Apache License 2.0", Copyleft: false},
	"BSD-2-CLAUSE": {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-CLAUSE": {Name: "BSD 3-Clause", Copyleft: false},
	"MPL-2.0":      {Name: "Mozilla Public License 2.0", Copyleft: true},
	"LGPL-2.1":     {Name: "GNU Lesser GPL v2.1", Copyleft: true},
	"LGPL-3.0":     {Name: "GNU Lesser GPL v3.0", Copyleft: true},
	"GPL-2.0":      {Name: "GNU GPL v2.0", Copyleft: true},
	"GPL-3.0":      {Name: "GNU GPL v3.0", Copyleft: true},
	"AGPL-3.0":     {Name: "GNU Affero GPL v3.0", Copyleft: true},
}

func isCopyleft(name string) bool {
	// direct spdx
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) ||
			strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// fallback
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "CC-BY-SA",
		"MPL", "MOZILLA PUBLIC LICENSE", "EPL", "CPL", "CDDL", "EUPL", "Affero", "OSL", "CeCILL",
		"GNU General Public License", "GNU Lesser General Public License", "Common Development and Distribution License",
		"Eclipse Public License", "Common Public License", "European Union Public License", "Open Software License",
	}
	up := strings.ToUpper(name)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

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

func getLicenseGroup(lic string) int {
	// used for sorting => copyleft(1), unknown(2), else(3)
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
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

// POM structs
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}
type MavenPOM struct {
	XMLName      xml.Name  `xml:"project"`
	Licenses     []License `xml:"licenses>license"`
	Dependencies []POMDep  `xml:"dependencies>dependency"`

	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// BFS node
type BFSNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*BFSNode
}

// BFSSection for each file type
type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// Flatten
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoInfo string
}

// finalData => final HTML
type finalData struct {
	Summary        string
	PomSections    []BFSSection
	TomlSections   []BFSSection
	GradleSections []BFSSection
}

// ----------------------------------------------------------------------
// 3) UTILS: SPLITGA, detectLicense, BFS expansions
// ----------------------------------------------------------------------

func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

func detectLicense(p *MavenPOM) string {
	if len(p.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(p.Licenses[0].Name)
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

// concurrency BFS worker
func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("[Worker] BFS => %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pm, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pm, err}
	}
}

// ----------------------------------------------------------------------
// 4) local disk caching => from license(1).go
// ----------------------------------------------------------------------

func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("   => in-mem cache => %s\n", key)
		return c.(*MavenPOM), nil
	}
	p, err := loadPOMFromDisk(g, a, v)
	if err == nil && p != nil {
		fmt.Printf("   => local disk => %s\n", key)
		pomCache.Store(key, p)
		return p, nil
	}
	fmt.Printf("   => not on disk => fetch => %s\n", key)
	rm, e2 := fetchRemotePOM(g, a, v)
	if e2 != nil {
		return nil, e2
	}
	pomCache.Store(key, rm)
	savePOMToDisk(g, a, v, rm)
	return rm, nil
}

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

func savePOMToDisk(g, a, v string, pom *MavenPOM) {
	path := localCachePath(g, a, v)
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		fmt.Printf("   => mkdirAll => %v\n", err)
		return
	}
	f, err := os.Create(path)
	if err != nil {
		fmt.Printf("   => create => %v\n", err)
		return
	}
	defer f.Close()
	dt, e2 := xml.MarshalIndent(pom, "", "  ")
	if e2 != nil {
		fmt.Printf("   => marshal => %v\n", e2)
		return
	}
	f.Write(dt)
	fmt.Printf("   => saved => %s\n", path)
}

func localCachePath(g, a, v string) string {
	gp := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, gp, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// fetch remote => central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gp := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gp, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gp, a, v, a, v)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		return pm, nil
	}
	if pm2, e2 := fetchPOMFromURL(urlG); e2 == nil && pm2 != nil {
		return pm2, nil
	}
	return nil, fmt.Errorf("could not fetch => %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	cl := http.Client{Timeout: fetchTimeout}
	resp, err := cl.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d => %s", resp.StatusCode, url)
	}
	dat, e2 := io.ReadAll(resp.Body)
	if e2 != nil {
		return nil, e2
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(dat))
	dec.Strict = false
	if e3 := dec.Decode(&mp); e3 != nil {
		return nil, e3
	}
	return &mp, nil
}

// ----------------------------------------------------------------------
// 5) BFS expansions for each file type
// ----------------------------------------------------------------------

func buildFullBFS(g, a, v, parent string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, v)
	if visited[key] {
		return nil
	}
	visited[key] = true

	if strings.ToLower(v) == "unknown" {
		return &BFSNode{
			Name:   g + "/" + a,
			Version: v,
			License: "Unknown",
			Parent: parent,
		}
	}
	// concurrency BFS => local disk => etc.
	pom, err := retrieveOrLoadPOM(g, a, v)
	n := &BFSNode{
		Name:   g + "/" + a,
		Version: v,
		Parent: parent,
		License: "Unknown",
	}
	if err != nil || pom == nil {
		return n
	}
	// detect license
	lic := detectLicense(pom)
	n.License  = lic
	n.Copyleft = isCopyleft(lic)

	// BFS children
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		cg, ca := d.GroupID, d.ArtifactID
		cv := d.Version
		if cv == "" {
			cv = "unknown"
		}
		child := buildFullBFS(cg, ca, cv, n.Name+"@"+v, visited)
		if child != nil {
			n.Transitive = append(n.Transitive, child)
		}
	}
	return n
}

func flattenBFSNode(n *BFSNode, lang string, out *[]FlatDep) {
	if n == nil {
		return
	}
	fd := FlatDep{
		Name:    n.Name,
		Version: n.Version,
		License: n.License,
		Parent:  n.Parent,
		Copyleft: n.Copyleft,
		Language: lang,
		RepoInfo: fmt.Sprintf("https://www.google.com/search?q=%s+%s", n.Name, n.Version),
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenBFSNode(c, lang, out)
	}
}

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
	for _, rt := range roots {
		flattenBFSNode(rt, lang, &flat)
	}
	sort.SliceStable(flat, func(i, j int) bool {
		g1 := getLicenseGroup(flat[i].License)
		g2 := getLicenseGroup(flat[j].License)
		return g1 < g2
	})
	return BFSSection{filePath, roots, flat}
}

// ----------------------------------------------------------------------
// 6) PARSE each file type EXACTLY as in your code
// ----------------------------------------------------------------------

// parseOnePomFile
func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(p string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, p)
		}
		return e
	})
	return out, err
}
func parseOnePomFile(filePath string) (map[string]string, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	if e2 := xml.Unmarshal(dat, &pom); e2 != nil {
		return nil, e2
	}
	res := make(map[string]string)
	for _, d := range pom.Dependencies {
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

// parseTomlFile
func findTOMLFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(p string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, p)
		}
		return e
	})
	return out, err
}
func parseTomlFile(filePath string) (map[string]string, error) {
	tree, err := toml.LoadFile(filePath)
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
		return nil, fmt.Errorf("'libraries' not valid in %s", filePath)
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

// parseBuildGradleFile
func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(p string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, p)
		}
		return e
	})
	return out, err
}
func parseBuildGradleFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	res := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
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
		res[g+"/"+a] = v
	}
	return res, nil
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
<h1>Consolidated BFS Report for POM, TOML, Gradle (Local .pom-cache approach)</h1>
<h2>Summary</h2>
<p>{{.Summary}}</p>

<h2>POM Files</h2>
{{range .PomSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Link</a></td>
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
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Link</a></td>
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
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Link</a></td>
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
	sum := fmt.Sprintf("%s@%s (License=%s)", n.Name, n.Version, n.License)
	css := "non-copyleft"
	if n.License == "Unknown" {
		css = "unknown"
	} else if n.Copyleft {
		css = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details class=\"" + css + "\"><summary>")
	sb.WriteString(template.HTMLEscapeString(sum))
	sb.WriteString("</summary>\n")
	if len(n.Transitive) > 0 {
		sb.WriteString("<ul>\n")
		for _, c := range n.Transitive {
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
// 8) MAIN => merges BFS expansions for POM, TOML, Gradle
// ----------------------------------------------------------------------

func main() {
	// spawn concurrency BFS
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	fmt.Println("[MAIN] scanning for pom.xml, .toml, build.gradle...")

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		fmt.Printf("[MAIN] Found POM => %s\n", pf)
		depMap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("   parseOnePomFile => %v\n", err)
			continue
		}
		ps := doBFSForDirect(depMap, pf, "maven")
		pomSections = append(pomSections, ps)
		totalPom += len(ps.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		fmt.Printf("[MAIN] Found TOML => %s\n", tf)
		deps, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("   parseTomlFile => %v\n", err)
			continue
		}
		if len(deps) == 0 {
			fmt.Printf("   no libs => %s\n", tf)
			continue
		}
		ts := doBFSForDirect(deps, tf, "toml")
		tomlSections = append(tomlSections, ts)
		totalToml += len(ts.Flattened)
	}

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		fmt.Printf("[MAIN] Found Gradle => %s\n", gf)
		dmap, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("   parseBuildGradleFile => %v\n", err)
			continue
		}
		if len(dmap) == 0 {
			fmt.Printf("   no gradle deps => %s\n", gf)
			continue
		}
		gs := doBFSForDirect(dmap, gf, "gradle")
		gradleSections = append(gradleSections, gs)
		totalGradle += len(gs.Flattened)
	}

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
		fmt.Printf("Template parse => %v\n", e2)
		return
	}
	out, e3 := os.Create("license-full-bfs-report.html")
	if e3 != nil {
		fmt.Printf("Create file => %v\n", e3)
		return
	}
	defer out.Close()

	if e4 := tmpl.Execute(out, data); e4 != nil {
		fmt.Printf("Execute => %v\n", e4)
		return
	}
	fmt.Println("[DONE] license-full-bfs-report.html => BFS expansions for POM, TOML, Gradle + local pom-cache!")
}

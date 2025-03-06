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
// 1) SHARED CONFIG
// ----------------------------------------------------------------------

const (
	bfsWorkerCount = 10
	fetchTimeout   = 30 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map
	parentVisit  sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// SPDx minimal, for license detection
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":        {Name: "MIT License", Copyleft: false},
	"Apache-2.0": {Name: "Apache License 2.0", Copyleft: false},
	"GPL-3.0":    {Name: "GNU GPL v3.0", Copyleft: true},
}

// ----------------------------------------------------------------------
// 2) LICENSE + SORT
// ----------------------------------------------------------------------

func isCopyleft(license string) bool {
	// 1) SPDx direct
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	// 2) fallback keywords
	keywords := []string{"GPL", "AGPL", "MPL", "EPL"}
	up := strings.ToUpper(license)
	for _, k := range keywords {
		if strings.Contains(up, k) {
			return true
		}
	}
	return false
}

// getLicenseGroup => for sorting: copyleft=1, unknown=2, rest=3
func getLicenseGroup(license string) int {
	if isCopyleft(license) {
		return 1
	} else if strings.EqualFold(license, "unknown") {
		return 2
	}
	return 3
}

// ----------------------------------------------------------------------
// 3) BFS concurrency
// ----------------------------------------------------------------------

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

func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		p, e := fetchRemotePOM(g, a, v)
		if e == nil && p != nil {
			pomCache.Store(key, p)
		}
		return p, e
	}
	rq := fetchRequest{g, a, v, make(chan fetchResult, 1)}
	pomRequests <- rq
	res := <-rq.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// ----------------------------------------------------------------------
// 4) fallbackVersionIfUnknown => if version is "unknown" => fetch "latest"
// ----------------------------------------------------------------------

func fallbackVersionIfUnknown(g, a, orig string) (string, error) {
	if strings.ToLower(orig) != "unknown" {
		return orig, nil
	}
	lat, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return lat, nil
}

// getLatestVersion => tries central, google
func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, e := fetchLatestVersionFromURL(urlC); e == nil && v != "" {
		return v, nil
	}
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v2, e2 := fetchLatestVersionFromURL(urlG); e2 == nil && v2 != "" {
		return v2, nil
	}
	return "", fmt.Errorf("cannot find latest for %s:%s", g, a)
}

func fetchLatestVersionFromURL(url string) (string, error) {
	cl := http.Client{Timeout: 15 * time.Second}
	resp, err := cl.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return "", fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	dat, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}
	type Versioning struct {
		Latest   string   `xml:"latest"`
		Release  string   `xml:"release"`
		Versions []string `xml:"versions>version"`
	}
	type Metadata struct {
		Versioning Versioning `xml:"versioning"`
	}
	var md Metadata
	if e2 := xml.Unmarshal(dat, &md); e2 != nil {
		return "", e2
	}
	if md.Versioning.Release != "" {
		return md.Versioning.Release, nil
	}
	if md.Versioning.Latest != "" {
		return md.Versioning.Latest, nil
	}
	if len(md.Versioning.Versions) > 0 {
		return md.Versioning.Versions[len(md.Versioning.Versions)-1], nil
	}
	return "", fmt.Errorf("no versions in metadata at %s", url)
}

// ----------------------------------------------------------------------
// 5) MAVEN POM struct + BFS
// ----------------------------------------------------------------------

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type MavenPOM struct {
	GroupID     string
	ArtifactID  string
	Version     string
	Licenses    []struct{ Name string } `xml:"licenses>license"`
	Dependencies []POMDep               `xml:"dependencies>dependency"`
}

// skip test/provided/system
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

// detectLicense => naive
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

// BFS fetch from central/google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		return pm, nil
	}
	if pm2, e2 := fetchPOMFromURL(urlG); e2 == nil && pm2 != nil {
		return pm2, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s", g, a, v)
}
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	cl := http.Client{Timeout: fetchTimeout}
	resp, err := cl.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	dat, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(dat))
	dec.Strict = false
	if e2 := dec.Decode(&pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

// BFS node
type BFSNode struct {
	Name     string
	Version  string
	License  string
	Copyleft bool
	Parent   string
	TopLevel string
	Children []*BFSNode
}

// full BFS => no limit
func doFullBFS(g, a, v, parent, top string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s@%s", g+"/"+a, v)
	if visited[key] {
		return nil
	}
	visited[key] = true
	eff, e2 := fallbackVersionIfUnknown(g, a, v)
	if e2 != nil {
		// remain unknown
		return &BFSNode{
			Name:   g + "/" + a,
			Version: v,
			License: "Unknown",
			Parent: parent,
			TopLevel: top,
		}
	}
	pom, err := concurrentFetchPOM(g, a, eff)
	if err != nil || pom == nil {
		return &BFSNode{
			Name:   g + "/" + a,
			Version: eff,
			License: "Unknown",
			Parent: parent,
			TopLevel: top,
		}
	}
	lic := detectLicense(pom)
	node := &BFSNode{
		Name:   g + "/" + a,
		Version: eff,
		License: lic,
		Copyleft: isCopyleft(lic),
		Parent: parent,
		TopLevel: top,
	}
	// BFS for children
	var kids []*BFSNode
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g2 := d.GroupID
		a2 := d.ArtifactID
		v2 := d.Version
		if v2 == "" {
			v2 = "unknown"
		}
		child := doFullBFS(g2, a2, v2, g+"/"+a+":"+eff, top, visited)
		if child != nil {
			kids = append(kids, child)
		}
	}
	node.Children = kids
	return node
}

// BFS expansions => <details>
func buildBFSHTML(n *BFSNode) string {
	sum := fmt.Sprintf("%s@%s (License: %s)", n.Name, n.Version, n.License)
	cls := "non-copyleft"
	if n.License == "Unknown" {
		cls = "unknown"
	} else if n.Copyleft {
		cls = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details><summary class=\"" + cls + "\">")
	sb.WriteString(template.HTMLEscapeString(sum))
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
	sb.WriteString("</details>\n")
	return sb.String()
}

// flatten BFS => final table
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	TopLevel string
	Copyleft bool
	RepoLink string
	Language string
}

func flattenBFSNode(n *BFSNode, lang string, out *[]FlatDep) {
	repoLink := buildRepoInfoLink(splitGA(n.Name))
	fd := FlatDep{
		Name:   n.Name,
		Version: n.Version,
		License: n.License,
		Parent: n.Parent,
		TopLevel: n.TopLevel,
		Copyleft: n.Copyleft,
		RepoLink: repoLink,
		Language: lang,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFSNode(c, lang, out)
	}
}
func buildRepoInfoLink(g, a string) string {
	if g == "" || a == "" {
		q := g + " " + a
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, "latest")
}

func splitGA(ga string) (string, string) {
	p := strings.SplitN(ga, "/", 2)
	if len(p) != 2 {
		return "", ""
	}
	return p[0], p[1]
}

// ----------------------------------------------------------------------
// 6) PARSE POM, TOML, GRADLE => BFS expansions
// ----------------------------------------------------------------------

type POMSection struct {
	FilePath  string
	DepsBFS   []*BFSNode
	Flattened []FlatDep
}
type TOMLSection struct {
	FilePath  string
	DepsBFS   []*BFSNode
	Flattened []FlatDep
}
type GradleSection struct {
	FilePath  string
	DepsBFS   []*BFSNode
	Flattened []FlatDep
}

// For each POM => BFS
func parseOnePomFile(filePath string) *POMSection {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		fmt.Printf("Error reading %s => %v\n", filePath, err)
		return nil
	}
	var pom MavenPOM
	xml.Unmarshal(dat, &pom)
	deps := pom.Dependencies
	var out []*BFSNode
	visited := make(map[string]bool)
	for _, d := range deps {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g := d.GroupID
		a := d.ArtifactID
		v := d.Version
		if v == "" {
			v = "unknown"
		}
		node := doFullBFS(g, a, v, "direct", g+"/"+a, visited)
		if node != nil {
			out = append(out, node)
		}
	}
	// flatten
	var flat []FlatDep
	for _, n := range out {
		flattenBFSNode(n, "maven", &flat)
	}
	// sort
	sort.SliceStable(flat, func(i, j int) bool {
		gi := getLicenseGroup(flat[i].License)
		gj := getLicenseGroup(flat[j].License)
		return gi < gj
	})
	return &POMSection{filePath, out, flat}
}

// For TOML
func parseOneTomlFile(filePath string) *TOMLSection {
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		fmt.Printf("Error reading TOML %s => %v\n", filePath, err)
		return nil
	}
	libObj := tree.Get("libraries")
	if libObj == nil {
		return nil
	}
	libTree, _ := libObj.(*toml.Tree)
	if libTree == nil {
		return nil
	}
	visited := make(map[string]bool)
	var out []*BFSNode
	for _, k := range libTree.Keys() {
		val := libTree.Get(k)
		sub, _ := val.(*toml.Tree)
		if sub == nil {
			continue
		}
		moduleStr, _ := sub.Get("module").(string)
		versionRef, _ := sub.Get("version.ref").(string)
		if moduleStr == "" || versionRef == "" {
			continue
		}
		parts := strings.SplitN(moduleStr, ":", 2)
		if len(parts) != 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		v := versionRef
		node := doFullBFS(g, a, v, "direct", g+"/"+a, visited)
		if node != nil {
			out = append(out, node)
		}
	}
	var flat []FlatDep
	for _, n := range out {
		flattenBFSNode(n, "toml", &flat)
	}
	sort.SliceStable(flat, func(i, j int) bool {
		gi := getLicenseGroup(flat[i].License)
		gj := getLicenseGroup(flat[j].License)
		return gi < gj
	})
	return &TOMLSection{filePath, out, flat}
}

// For Gradle
func parseOneGradleFile(filePath string) *GradleSection {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		fmt.Printf("Error reading Gradle %s => %v\n", filePath, err)
		return nil
	}
	content := string(dat)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	visited := make(map[string]bool)
	var out []*BFSNode
	for _, m := range matches {
		coord := m[2]
		p := strings.Split(coord, ":")
		if len(p) < 2 {
			continue
		}
		g := p[0]
		a := p[1]
		v := "unknown"
		if len(p) >= 3 {
			v = p[2]
		}
		node := doFullBFS(g, a, v, "direct", g+"/"+a, visited)
		if node != nil {
			out = append(out, node)
		}
	}
	var flat []FlatDep
	for _, n := range out {
		flattenBFSNode(n, "gradle", &flat)
	}
	sort.SliceStable(flat, func(i, j int) bool {
		gi := getLicenseGroup(flat[i].License)
		gj := getLicenseGroup(flat[j].License)
		return gi < gj
	})
	return &GradleSection{filePath, out, flat}
}

// BFS expansions => <details>
func buildBFSExpansionsHTML(bfs []*BFSNode) string {
	if len(bfs) == 0 {
		return "<p>No BFS expansions found.</p>"
	}
	var sb strings.Builder
	for _, n := range bfs {
		sb.WriteString(buildBFSHTML(n))
	}
	return sb.String()
}

// ----------------------------------------------------------------------
// 7) FINAL HTML
// ----------------------------------------------------------------------

var finalTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Full BFS License Report</title>
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
<h1>Full BFS License Report</h1>
<h2>Summary</h2>
<p>{{.Summary}}</p>

{{range .PomSections}}
<h2>POM Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this POM file.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Maven/Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.BFSHTML}}
</div>
<hr/>
{{end}}

{{range .TomlSections}}
<h2>TOML Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this TOML file.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Maven/Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.BFSHTML}}
</div>
<hr/>
{{end}}

{{range .GradleSections}}
<h2>Gradle Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this Gradle file.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Maven/Repo Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.BFSHTML}}
</div>
<hr/>
{{end}}

</body>
</html>
`

type PomHTMLSection struct {
	FilePath  string
	BFSHTML   template.HTML
	Flattened []FlatDep
}
type TomlHTMLSection struct {
	FilePath  string
	BFSHTML   template.HTML
	Flattened []FlatDep
}
type GradleHTMLSection struct {
	FilePath  string
	BFSHTML   template.HTML
	Flattened []FlatDep
}

// We'll store final data in a struct
type finalData struct {
	Summary       string
	PomSections   []PomHTMLSection
	TomlSections  []TomlHTMLSection
	GradleSections []GradleHTMLSection
}

// ----------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------

func main() {
	// start BFS concurrency
	for i := 0; i < bfsWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// parse poms
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []PomHTMLSection
	var totalPomTop int
	for _, pf := range pomFiles {
		section := parseOnePomFile(pf)
		if section == nil {
			continue
		}
		totalPomTop += len(section.Flattened)
		// BFS expansions
		var sb strings.Builder
		for _, b := range section.DepsBFS {
			sb.WriteString(buildBFSHTML(b))
		}
		pomSections = append(pomSections, PomHTMLSection{
			FilePath:  pf,
			BFSHTML:   template.HTML(sb.String()),
			Flattened: section.Flattened,
		})
	}

	// parse tomls
	tomlFiles, _ := findTOMLFile(".")
	var tomlSections []TomlHTMLSection
	var totalToml int
	for _, tf := range tomlFiles {
		section := parseOneTomlFile(tf)
		if section == nil {
			continue
		}
		totalToml += len(section.Flattened)
		var sb strings.Builder
		for _, b := range section.DepsBFS {
			sb.WriteString(buildBFSHTML(b))
		}
		tomlSections = append(tomlSections, TomlHTMLSection{
			FilePath:  tf,
			BFSHTML:   template.HTML(sb.String()),
			Flattened: section.Flattened,
		})
	}

	// parse gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []GradleHTMLSection
	var totalGradle int
	for _, gf := range gradleFiles {
		section := parseOneGradleFile(gf)
		if section == nil {
			continue
		}
		totalGradle += len(section.Flattened)
		var sb strings.Builder
		for _, b := range section.DepsBFS {
			sb.WriteString(buildBFSHTML(b))
		}
		gradleSections = append(gradleSections, GradleHTMLSection{
			FilePath:  gf,
			BFSHTML:   template.HTML(sb.String()),
			Flattened: section.Flattened,
		})
	}

	// concurrency close
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// count copyleft
	copyleftCount := 0
	for _, sec := range pomSections {
		for _, dep := range sec.Flattened {
			if isCopyleft(dep.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range tomlSections {
		for _, dep := range sec.Flattened {
			if isCopyleft(dep.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range gradleSections {
		for _, dep := range sec.Flattened {
			if isCopyleft(dep.License) {
				copyleftCount++
			}
		}
	}
	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d",
		totalPomTop, totalToml, totalGradle, copyleftCount)

	data := finalData{
		Summary: summary,
		PomSections:   pomSections,
		TomlSections:  tomlSections,
		GradleSections: gradleSections,
	}

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"isCopyleft": isCopyleft,
	}).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error:", err)
		return
	}
	out, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Println("Create file error:", err)
		return
	}
	defer out.Close()

	if e2 := tmpl.Execute(out, data); e2 != nil {
		fmt.Println("Template exec error:", e2)
		return
	}
	fmt.Println("license-full-bfs-report.html generated successfully!")
}

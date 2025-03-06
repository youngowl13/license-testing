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

// ------------------------------------------------------------------------------------
// 1) SHARED GLOBALS / CONFIG
// ------------------------------------------------------------------------------------

const (
	numWorkers    = 5
	fetchTimeout  = 15 * time.Second
	maxBFSLevels  = 2 // We'll only BFS up to 2 levels (direct + 1 transitive layer).
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map
	parentVisit  sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// Minimal SPDx => (FriendlyName, Copyleft)
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":        {Name: "MIT License", Copyleft: false},
	"Apache-2.0": {Name: "Apache License 2.0", Copyleft: false},
	"GPL-3.0":    {Name: "GNU GPL v3.0", Copyleft: true},
}

// getLicenseGroup => for sorting: copyleft => 1, unknown => 2, others => 3
func getLicenseGroup(license string) int {
	if isCopyleft(license) {
		return 1
	} else if strings.EqualFold(license, "unknown") {
		return 2
	}
	return 3
}
func isCopyleft(license string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	return false
}

// ------------------------------------------------------------------------------------
// 2) BFS concurrency: we define fetchRequest => fetchRemotePOM => concurrency
// ------------------------------------------------------------------------------------

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

func worker() {
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
	req := fetchRequest{g, a, v, make(chan fetchResult, 1)}
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// ------------------------------------------------------------------------------------
// 3) The “partial BFS” => we only do 2 levels
// ------------------------------------------------------------------------------------

func partialBFSDependencies(g, a, v string, depth int) (*MavenPOM, []DepLink, error) {
	// If depth >= maxBFSLevels, stop BFS
	if depth >= maxBFSLevels {
		return nil, nil, nil
	}
	// fetch pom
	pom, err := concurrentFetchPOM(g, a, v)
	if err != nil {
		return nil, nil, err
	}
	if pom == nil {
		return nil, nil, nil
	}
	var out []DepLink
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
		out = append(out, DepLink{g2, a2, v2})
	}
	return pom, out, nil
}

// we store a BFS link
type DepLink struct {
	Group string
	Art   string
	Ver   string
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

// ------------------------------------------------------------------------------------
// 4) parseVersionRange, parseManagedVersions, retrieveOrLoadPOM, splitGA
//     – stubs or minimal to avoid "undefined" errors
// ------------------------------------------------------------------------------------

func parseVersionRange(ver string) string {
	ver = strings.TrimSpace(ver)
	if strings.HasPrefix(ver, "[") || strings.HasPrefix(ver, "(") {
		// Just a naive approach, partial BFS
		return strings.Trim(ver, "[]() ")
	}
	return ver
}
func parseManagedVersions(*MavenPOM) map[string]string {
	// minimal stub
	return make(map[string]string)
}
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	// minimal stub => call fetchRemotePOM
	return fetchRemotePOM(g, a, v)
}
func splitGA(ga string) (string, string) {
	p := strings.SplitN(ga, "/", 2)
	if len(p) != 2 {
		return "", ""
	}
	return p[0], p[1]
}

// ------------------------------------------------------------------------------------
// 5) MAVEN POM struct
// ------------------------------------------------------------------------------------

type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type MavenPOM struct {
	GroupID        string
	ArtifactID     string
	Version        string
	Licenses       []struct{ Name string } `xml:"licenses>license"`
	Dependencies   []POMDep                `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
}

// fetchRemotePOM => tries central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
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

// naive license detection
func detectLicense(p *MavenPOM) string {
	if len(p.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(p.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	// partial check
	if strings.Contains(strings.ToLower(lic), "apache") {
		return "Apache-2.0"
	}
	if strings.Contains(strings.ToLower(lic), "gpl") {
		return "GPL-3.0"
	}
	return lic
}

// ------------------------------------------------------------------------------------
// 6) PARTIAL BFS NODE
// ------------------------------------------------------------------------------------

// We limit BFS to depth=2
type PartialNode struct {
	Name      string
	Version   string
	License   string
	Copyleft  bool
	Children  []*PartialNode
}

// ------------------------------------------------------------------------------------
// 7) PARSING FILES: pom.xml, .toml, build.gradle => direct deps
// ------------------------------------------------------------------------------------

func findPoms(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}
func parsePomFile(filePath string) map[string]string {
	res := make(map[string]string)
	dat, _ := os.ReadFile(filePath)
	var pom MavenPOM
	xml.Unmarshal(dat, &pom)
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g := d.GroupID
		a := d.ArtifactID
		v := d.Version
		if v == "" {
			v = "unknown"
		}
		key := g + "/" + a
		res[key] = v
	}
	return res
}

// TOML
func findTomls(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(p string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, p)
		}
		return nil
	})
	return out, err
}
func parseTomlFile(path string) map[string]string {
	tree, err := toml.LoadFile(path)
	if err != nil {
		return nil
	}
	versTable := tree.Get("versions")
	libraries := tree.Get("libraries")
	res := make(map[string]string)
	if libraries == nil {
		return res
	}
	libTree, _ := libraries.(*toml.Tree)
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
		key := g + "/" + a
		// naive
		res[key] = versionRef
	}
	return res
}

// GRADLE
type ExtendedDepInfo struct {
	Display string
	Lookup  string
}
func findGradle(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}
func parseBuildGradle(filePath string) map[string]ExtendedDepInfo {
	res := make(map[string]ExtendedDepInfo)
	dat, _ := os.ReadFile(filePath)
	content := string(dat)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
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
		key := g + "/" + a + "@" + v
		res[key] = ExtendedDepInfo{v, v}
	}
	return res
}

// ------------------------------------------------------------------------------------
// 8) BFS expansions => partial BFS => direct + 1 level
// We'll just do a partial BFS in the final expansions for clarity
// ------------------------------------------------------------------------------------

// We'll show partial expansions in the final HTML
// For example, if we have direct "g/a@v" => we fetch 2nd-level children but no deeper
// We'll define "PartialDep" for expansions

type PartialDep struct {
	Name     string
	Version  string
	License  string
	Copyleft bool
	Children []PartialDep
}

// BFS expansions using partial BFS
func partialBFSExpand(g, a, ver string, depth int) PartialDep {
	p := PartialDep{
		Name:    g + "/" + a,
		Version: ver,
		License: "Unknown",
	}
	if depth >= maxBFSLevels {
		return p
	}
	// fetch
	pom, links, err := partialBFSDependencies(g, a, ver, depth)
	if err == nil && pom != nil {
		p.License = detectLicense(pom)
		p.Copyleft = isCopyleft(p.License)
		if len(links) > 0 {
			for _, lk := range links {
				p.Children = append(p.Children,
					partialBFSExpand(lk.Group, lk.Art, lk.Ver, depth+1))
			}
		}
	}
	return p
}

// convert partial BFS expansions to <details>
func partialDetailsHTML(dep PartialDep) string {
	sum := fmt.Sprintf("%s@%s (License: %s)", dep.Name, dep.Version, dep.License)
	cls := "non-copyleft"
	if dep.License == "Unknown" {
		cls = "unknown"
	} else if dep.Copyleft {
		cls = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details><summary class=\"" + cls + "\">")
	sb.WriteString(template.HTMLEscapeString(sum))
	sb.WriteString("</summary>\n")
	if len(dep.Children) > 0 {
		sb.WriteString("<ul>\n")
		for _, ch := range dep.Children {
			sb.WriteString("<li>")
			sb.WriteString(partialDetailsHTML(ch))
			sb.WriteString("</li>\n")
		}
		sb.WriteString("</ul>\n")
	}
	sb.WriteString("</details>\n")
	return sb.String()
}

// ------------------------------------------------------------------------------------
// 9) Flatten table rows, single link column => "RepoInfoURL"
// ------------------------------------------------------------------------------------

type FlatRow struct {
	Name      string
	Version   string
	License   string
	Parent    string
	TopLevel  string
	RepoInfo  string
}

func buildRepoInfoLink(g, a, v string) string {
	if g == "" || a == "" {
		q := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s",
		a, g, a, v)
}

// We'll define partial BFS for the table too: direct dependencies only (1 level)
func partialFlattenDirect(deps map[string]string, topKey string) []FlatRow {
	var out []FlatRow
	for ga, ver := range deps {
		g, a := splitGA(ga)
		link := buildRepoInfoLink(g, a, ver)
		out = append(out, FlatRow{
			Name: ga, Version: ver,
			License: "Unknown",
			Parent:  "direct",
			TopLevel: topKey,
			RepoInfo: link,
		})
	}
	return out
}

// ------------------------------------------------------------------------------------
// 10) Final HTML
// We'll do partial BFS expansions for each direct dependency
// ------------------------------------------------------------------------------------

var partialTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Partial BFS Report</title>
<style>
body{font-family:Arial,sans-serif;margin:20px}
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
<h1>Partial BFS License Report (2 levels only)</h1>

<h2>Summary</h2>
<p>{{.Summary}}</p>

{{range .Poms}}
<h2>POM Partial BFS</h2>
<p>File path: {{.FilePath}}</p>
<p>Direct Dependencies Table (1 level only):</p>
{{if eq (len .Rows) 0}}
<p>No direct deps found in {{.FilePath}}</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Repo Info</th>
</tr>
{{range .Rows}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td>{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Link</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>2-Level BFS Expansions</h3>
<div>
{{.BFSHTML}}
</div>
<hr/>
{{end}}

</body>
</html>
`

// We'll define final data for each POM file
type PomSection struct {
	FilePath string
	Rows     []FlatRow
	BFSHTML  template.HTML
}

func main() {
	// start concurrency
	for i := 0; i < numWorkers; i++ {
		wgWorkers.Add(1)
		go worker()
	}

	// find pom.xml
	poms, _ := findPoms(".")
	var results []PomSection
	totalDeps := 0
	for _, pf := range poms {
		depMap := parsePomFile(pf)
		totalDeps += len(depMap)
		// partial BFS expansions for each direct
		// We'll just do BFS expansions for each direct
		var expansions strings.Builder
		for ga, ver := range depMap {
			g, a := splitGA(ga)
			ver2, _ := fallbackVersionIfUnknown(g, a, ver)
			// partial BFS expansions
			node := partialBFSExpand(g, a, ver2, 0)
			expansions.WriteString(partialDetailsHTML(node))
		}
		// direct table flatten
		rows := partialFlattenDirect(depMap, "pomFile:"+pf)
		results = append(results, PomSection{
			FilePath: pf,
			Rows:     rows,
			BFSHTML:  template.HTML(expansions.String()),
		})
	}

	// close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	summary := fmt.Sprintf("Found %d POM direct deps total (2-level partial BFS).", totalDeps)
	data := struct {
		Summary string
		Poms    []PomSection
	}{
		summary,
		results,
	}

	tmpl, err := template.New("partial").Parse(partialTemplate)
	if err != nil {
		fmt.Println("Template parse error:", err)
		return
	}
	f, err := os.Create("partial-bfs-report.html")
	if err != nil {
		fmt.Println("Create file error:", err)
		return
	}
	defer f.Close()

	if e2 := tmpl.Execute(f, data); e2 != nil {
		fmt.Println("Template exec error:", e2)
		return
	}
	fmt.Println("partial-bfs-report.html generated successfully (2-level BFS).")
}

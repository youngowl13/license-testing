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
// 1) GLOBAL CONFIG & VARIABLES
// ----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"       // local disk cache directory for POM files
	fetchTimeout     = 30 * time.Second   // HTTP fetch timeout
	workerCount      = 6                  // number of concurrent fetch workers
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" => *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) UTILS: SCOPE, COPYLEFT, SORTING, SPLIT
// ----------------------------------------------------------------------

// skipScope returns true if the dependency's scope is test/provided/system or if it's optional.
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

// Comprehensive set of copyleft keywords.
var copyleftKeywords = []string{
	"GPL", "LGPL", "AGPL", "CC-BY-SA", "MPL", "EPL", "CPL", "CDDL", "EUPL",
	"OSL", "CeCILL", "GNU GENERAL PUBLIC LICENSE",
	"GNU LESSER GENERAL PUBLIC LICENSE", "GNU AFFERO GENERAL PUBLIC LICENSE",
	"MOZILLA PUBLIC LICENSE", "COMMON DEVELOPMENT AND DISTRIBUTION LICENSE",
	"ECLIPSE PUBLIC LICENSE", "COMMON PUBLIC LICENSE", "EUROPEAN UNION PUBLIC LICENSE",
	"OPEN SOFTWARE LICENSE", "CREATIVE COMMONS ATTRIBUTION-SHAREALIKE",
}

func isCopyleft(license string) bool {
	up := strings.ToUpper(license)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// For sorting: copyleft = 1, unknown = 2, others = 3.
func getLicenseGroup(lic string) int {
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
}

// splitGA splits a string of format "group/artifact" into its two parts.
func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// ----------------------------------------------------------------------
// 3) DATA STRUCTURES: POM, BFS Node, FlatDep, BFSSection
// ----------------------------------------------------------------------

// Structures for Maven POM parsing.
type PomLicense struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type MavenPOM struct {
	XMLName      xml.Name     `xml:"project"`
	Licenses     []PomLicense `xml:"licenses>license"`
	Dependencies []POMDep     `xml:"dependencies>dependency"`
	GroupID      string       `xml:"groupId"`
	ArtifactID   string       `xml:"artifactId"`
	Version      string       `xml:"version"`
}

// BFSNode represents a node in the dependency tree.
type BFSNode struct {
	Name     string     // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string       // e.g. "direct" or "group/artifact@version"
	Children []*BFSNode
}

// FlatDep is a flattened dependency row for the final report.
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoLink string
}

// BFSSection holds the BFS expansion and flattened table for one file.
type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// ----------------------------------------------------------------------
// 4) MAVEN LICENSE FETCHING LOGIC
// ----------------------------------------------------------------------

// detectLicense extracts the license from a MavenPOM.
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

// ----------------------------------------------------------------------
// 5) CONCURRENT FETCHING (WITH LOCAL DISK CACHING)
// ----------------------------------------------------------------------

// fetchRequest and fetchResult for concurrency.
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

// pomWorker runs as a goroutine to fetch POM files.
func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		p, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: p, Err: err}
	}
}

// localCachePath builds a file path for storing a POM.
func localCachePath(g, a, v string) string {
	gp := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, gp, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// savePOMToDisk saves the given MavenPOM to disk.
func savePOMToDisk(g, a, v string, mp *MavenPOM) {
	path := localCachePath(g, a, v)
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		fmt.Printf("[savePOMToDisk] mkdirAll error: %v\n", err)
		return
	}
	f, err := os.Create(path)
	if err != nil {
		fmt.Printf("[savePOMToDisk] create error: %v\n", err)
		return
	}
	defer f.Close()
	data, err := xml.MarshalIndent(mp, "", "  ")
	if err != nil {
		fmt.Printf("[savePOMToDisk] marshal error: %v\n", err)
		return
	}
	f.Write(data)
	fmt.Printf("[savePOMToDisk] Saved POM to %s\n", path)
}

// loadPOMFromDisk loads a MavenPOM from disk if available.
func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if err := dec.Decode(&mp); err != nil {
		return nil, err
	}
	return &mp, nil
}

// fetchRemotePOM attempts to fetch a POM from Maven Central first, then Google Maven.
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gp := strings.ReplaceAll(g, ".", "/")
	centralURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gp, a, v, a, v)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gp, a, v, a, v)
	p, err := fetchPOMFromURL(centralURL)
	if err == nil && p != nil {
		return p, nil
	}
	p2, err2 := fetchPOMFromURL(googleURL)
	if err2 == nil && p2 != nil {
		return p2, nil
	}
	if err != nil {
		return nil, err2
	}
	return nil, err2
}

// fetchPOMFromURL performs an HTTP GET and decodes the POM XML.
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	fmt.Printf("[fetchPOMFromURL] GET %s\n", url)
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d at %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if err := dec.Decode(&mp); err != nil {
		return nil, err
	}
	return &mp, nil
}

// retrieveOrLoadPOM checks in-memory cache, then disk, then fetches remotely.
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("[retrieveOrLoadPOM] In-memory cache hit: %s\n", key)
		return c.(*MavenPOM), nil
	}
	mp, err := loadPOMFromDisk(g, a, v)
	if err == nil && mp != nil {
		fmt.Printf("[retrieveOrLoadPOM] Loaded from disk: %s\n", key)
		pomCache.Store(key, mp)
		return mp, nil
	}
	fmt.Printf("[retrieveOrLoadPOM] Fetching remotely: %s\n", key)
	remote, err2 := fetchRemotePOM(g, a, v)
	if err2 != nil {
		return nil, err2
	}
	pomCache.Store(key, remote)
	savePOMToDisk(g, a, v, remote)
	return remote, nil
}

// ----------------------------------------------------------------------
// 6) BFS EXPANSION FUNCTIONS
// ----------------------------------------------------------------------

// buildFullBFS recursively builds a BFS tree for a dependency.
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
	if strings.ToLower(v) == "unknown" {
		return node
	}
	p, err := retrieveOrLoadPOM(g, a, v)
	if err != nil || p == nil {
		return node
	}
	lic := detectLicense(p)
	node.License = lic
	node.Copyleft = isCopyleft(lic)
	for _, d := range p.Dependencies {
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

// flattenBFSNode flattens the BFS tree into a slice for the report.
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

// doBFSForDirect starts BFS on a map of direct dependencies and flattens the result.
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

// ----------------------------------------------------------------------
// 7) REPORT LINK LOGIC: Build Repo Link for Display
// ----------------------------------------------------------------------

// buildRepoLink returns a URL for display purposes.
// If group starts with "com.android" or "androidx", it returns a Google Maven UI link;
// otherwise, it returns a link to mvnrepository.com.
func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" || v == "" {
		return fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s", g, a, v)
	}
	if strings.HasPrefix(g, "com.android") || strings.HasPrefix(g, "androidx") {
		return fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", g, a, v)
	}
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", g, a, v)
}

// ----------------------------------------------------------------------
// 8) PARSING FUNCTIONS FOR EACH FILE TYPE
// ----------------------------------------------------------------------

// POM parsing
func parseOnePomFile(path string) (map[string]string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	if err := xml.Unmarshal(data, &mp); err != nil {
		return nil, err
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
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// TOML parsing
func parseTomlFile(path string) (map[string]string, error) {
	tree, err := toml.LoadFile(path)
	if err != nil {
		return nil, err
	}
	res := make(map[string]string)
	libs := tree.Get("libraries")
	if libs == nil {
		return res, nil
	}
	libTree, ok := libs.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", path)
	}
	for _, k := range libTree.Keys() {
		val := libTree.Get(k)
		sub, ok := val.(*toml.Tree)
		if !ok {
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
		res[g+"/"+a] = verRef
	}
	return res, nil
}

func findTOMLFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// Gradle parsing
func parseBuildGradleFile(path string) (map[string]string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	content := string(data)
	res := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		coord := m[2]
		parts := strings.Split(coord, ":")
		if len(parts) < 2 {
			continue
		}
		g, a := parts[0], parts[1]
		v := "unknown"
		if len(parts) >= 3 {
			v = parts[2]
		}
		res[g+"/"+a] = v
	}
	return res, nil
}

func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// ----------------------------------------------------------------------
// 9) FINAL HTML REPORT TEMPLATE
// ----------------------------------------------------------------------

var finalTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>license-full-bfs-report</title>
<style>
body { font-family: Arial, sans-serif; margin: 20px; }
h1, h2 { color: #2c3e50; }
table { width: 100%; border-collapse: collapse; margin-bottom: 20px; }
th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
th { background: #f2f2f2; }
.copyleft { background: #f8d7da; color: #721c24; }
.unknown { background: #ffff99; color: #333; }
.non-copyleft { background: #d4edda; color: #155724; }
details { margin: 4px 0; }
summary { cursor: pointer; font-weight: bold; }
</style>
</head>
<body>
<h1>Consolidated BFS Report for POM, TOML, Gradle</h1>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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

// buildBFSHTML recursively renders a BFS node as a <details> block.
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
			sb.WriteString("<li>" + buildBFSHTML(c) + "</li>\n")
		}
		sb.WriteString("</ul>\n")
	}
	sb.WriteString("</details>")
	return sb.String()
}

// ----------------------------------------------------------------------
// 10) PARSING FUNCTIONS (POM, TOML, Gradle)
// ----------------------------------------------------------------------

// POM parsing
func parseOnePomFile(path string) (map[string]string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var mp MavenPOM
	if err := xml.Unmarshal(data, &mp); err != nil {
		return nil, err
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
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// TOML parsing
func parseTomlFile(path string) (map[string]string, error) {
	tree, err := toml.LoadFile(path)
	if err != nil {
		return nil, err
	}
	res := make(map[string]string)
	libs := tree.Get("libraries")
	if libs == nil {
		return res, nil
	}
	libTree, ok := libs.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", path)
	}
	for _, k := range libTree.Keys() {
		val := libTree.Get(k)
		sub, ok := val.(*toml.Tree)
		if !ok {
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
		res[g+"/"+a] = verRef
	}
	return res, nil
}

func findTOMLFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// Gradle parsing
func parseBuildGradleFile(path string) (map[string]string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	content := string(data)
	res := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		coord := m[2]
		parts := strings.Split(coord, ":")
		if len(parts) < 2 {
			continue
		}
		g, a := parts[0], parts[1]
		v := "unknown"
		if len(parts) >= 3 {
			v = parts[2]
		}
		res[g+"/"+a] = v
	}
	return res, nil
}

func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return err
	})
	return out, err
}

// ----------------------------------------------------------------------
// 11) FINAL HTML REPORT
// ----------------------------------------------------------------------

type FinalData struct {
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
body { font-family: Arial, sans-serif; margin: 20px; }
h1, h2 { color: #2c3e50; }
table { width: 100%; border-collapse: collapse; margin-bottom: 20px; }
th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
th { background: #f2f2f2; }
.copyleft { background: #f8d7da; color: #721c24; }
.unknown { background: #ffff99; color: #333; }
.non-copyleft { background: #d4edda; color: #155724; }
details { margin: 4px 0; }
summary { cursor: pointer; font-weight: bold; }
</style>
</head>
<body>
<h1>Consolidated BFS Report for POM, TOML, Gradle</h1>
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
			<td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
			<td>{{.Parent}}</td>
			<td>{{.Language}}</td>
			<td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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
			<td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
			<td>{{.Parent}}</td>
			<td>{{.Language}}</td>
			<td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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
			<td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
			<td>{{.Parent}}</td>
			<td>{{.Language}}</td>
			<td><a href="{{.RepoLink}}" target="_blank">Link</a></td>
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

// buildBFSHTML recursively renders a BFS node as a <details> block.
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
			sb.WriteString("<li>" + buildBFSHTML(c) + "</li>\n")
		}
		sb.WriteString("</ul>\n")
	}
	sb.WriteString("</details>")
	return sb.String()
}

// ----------------------------------------------------------------------
// 12) MAIN FUNCTION: Consolidate everything and generate the HTML report
// ----------------------------------------------------------------------

func main() {
	// Start BFS workers
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	fmt.Println("[MAIN] Scanning for pom.xml, .toml, and build.gradle files...")

	// POM Files
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	totalPom := 0
	for _, pf := range pomFiles {
		fmt.Printf("[MAIN] Found POM: %s\n", pf)
		deps, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("[POM] Parse error: %v\n", err)
			continue
		}
		section := doBFSForDirect(deps, pf, "maven")
		pomSections = append(pomSections, section)
		totalPom += len(section.Flattened)
	}

	// TOML Files
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	totalToml := 0
	for _, tf := range tomlFiles {
		fmt.Printf("[MAIN] Found TOML: %s\n", tf)
		deps, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("[TOML] Parse error: %v\n", err)
			continue
		}
		if len(deps) == 0 {
			continue
		}
		section := doBFSForDirect(deps, tf, "toml")
		tomlSections = append(tomlSections, section)
		totalToml += len(section.Flattened)
	}

	// Gradle Files
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	totalGradle := 0
	for _, gf := range gradleFiles {
		fmt.Printf("[MAIN] Found Gradle: %s\n", gf)
		deps, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("[Gradle] Parse error: %v\n", err)
			continue
		}
		if len(deps) == 0 {
			continue
		}
		section := doBFSForDirect(deps, gf, "gradle")
		gradleSections = append(gradleSections, section)
		totalGradle += len(section.Flattened)
	}

	// Shutdown BFS workers
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Count copyleft dependencies
	copyleftCount := 0
	for _, sec := range pomSections {
		for _, d := range sec.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range tomlSections {
		for _, d := range sec.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range gradleSections {
		for _, d := range sec.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	summary := fmt.Sprintf("POM total=%d, TOML total=%d, Gradle total=%d, Copyleft=%d", totalPom, totalToml, totalGradle, copyleftCount)

	// Prepare final data for report
	finalData := struct {
		Summary        string
		PomSections    []BFSSection
		TomlSections   []BFSSection
		GradleSections []BFSSection
	}{
		Summary:        summary,
		PomSections:    pomSections,
		TomlSections:   tomlSections,
		GradleSections: gradleSections,
	}

	funcMap := template.FuncMap{
		"isCopyleft":  isCopyleft,
		"buildBFSHTML": func(n *BFSNode) template.HTML { return template.HTML(buildBFSHTML(n)) },
	}
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Printf("[MAIN] Template parse error: %v\n", err)
		return
	}
	out, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Printf("[MAIN] Create file error: %v\n", err)
		return
	}
	defer out.Close()

	if err := tmpl.Execute(out, finalData); err != nil {
		fmt.Printf("[MAIN] Template execute error: %v\n", err)
		return
	}
	fmt.Println("[DONE] license-full-bfs-report.html generated successfully!")
}

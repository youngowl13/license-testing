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

// ----------------------------------------------------------------------
// 2) UTILS: SCOPE, COPYLEFT, SORTING
// ----------------------------------------------------------------------

// skipScope: skip dependencies with scope test/provided/system or optional true.
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

// Comprehensive copyleft keywords.
var copyleftKeywords = []string{
	"GPL", "LGPL", "AGPL", "CC-BY-SA", "MPL", "EPL", "CPL", "CDDL", "EUPL",
	"OSL", "CeCILL", "GNU GENERAL PUBLIC LICENSE", "GNU LESSER GENERAL PUBLIC LICENSE",
	"GNU AFFERO GENERAL PUBLIC LICENSE", "MOZILLA PUBLIC LICENSE", "COMMON DEVELOPMENT AND DISTRIBUTION LICENSE",
	"ECLIPSE PUBLIC LICENSE", "COMMON PUBLIC LICENSE", "EUROPEAN UNION PUBLIC LICENSE", "OPEN SOFTWARE LICENSE",
	"CREATIVE COMMONS ATTRIBUTION-SHAREALIKE",
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

// For sorting: copyleft = 1, unknown = 2, else = 3.
func getLicenseGroup(lic string) int {
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
}

// splitGA: splits "group/artifact" into its two parts.
func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// ----------------------------------------------------------------------
// 3) DATA STRUCTURES: POM, BFS, Report Row
// ----------------------------------------------------------------------

// Maven POM structures
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

// BFS node for dependency tree.
type BFSNode struct {
	Name     string      // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string // e.g. "direct" or "group/artifact@version"
	Children []*BFSNode
}

// FlatDep: a flattened dependency row for final report.
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoLink string
}

// BFSSection: one section per input file.
type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// ----------------------------------------------------------------------
// 4) MAVEN FETCHING LOGIC
// ----------------------------------------------------------------------

// For BFS concurrency: request/response types.
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

// pomWorker: worker routine for fetching POM files.
func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		p, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: p, Err: err}
	}
}

// Local caching: build local cache path.
func localCachePath(g, a, v string) string {
	gpath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, gpath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

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
	fmt.Printf("[savePOMToDisk] Saved to %s\n", path)
}

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

// fetchRemotePOM: tries Maven Central then Google Maven (sequentially).
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	centralURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)

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

// fetchPOMFromURL: HTTP GET and XML parse.
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

// retrieveOrLoadPOM: check in-memory, then local disk, then fetch remotely.
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
// 5) BFS EXPANSIONS
// ----------------------------------------------------------------------

// buildFullBFS recursively builds a dependency tree using BFS logic.
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
	// If version is unknown, do not expand further.
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

// flattenBFSNode flattens a BFS tree into a slice for the final table.
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

// doBFSForDirect: given a map of direct dependencies, build BFS tree and flatten.
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
// 6) REPORT LINK LOGIC (Display logic)
// ----------------------------------------------------------------------

// buildRepoLink generates a URL for the report. If group starts with "com.android" or "androidx", use Google Maven UI.
func buildRepoLink(group, artifact, version string) string {
	if group == "" || artifact == "" || version == "" {
		return fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s", group, artifact, version)
	}
	if strings.HasPrefix(group, "com.android") || strings.HasPrefix(group, "androidx") {
		return fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", group, artifact, version)
	}
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", group, artifact, version)
}

// ----------------------------------------------------------------------
// 7) PARSING FILES (POM, TOML, Gradle)
// ----------------------------------------------------------------------

// POM
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
	err := filepath.Walk(root, func(p string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, p)
		}
		return err
	})
	return out, err
}

// TOML
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
	err := filepath.Walk(root, func(p string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, p)
		}
		return err
	})
	return out, err
}

// Gradle
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
	err := filepath.Walk(root, func(p string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, p)
		}
		return err
	})
	return out, err
}

// ----------------------------------------------------------------------
// 8) FINAL HTML REPORT TEMPLATE (using a raw string literal)
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

// buildBFSHTML: renders a BFS node recursively as a <details> block.
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
// 9) PARSING FUNCTIONS FOR EACH FILE TYPE
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
// 10) MAIN: Consolidate BFS for POM, TOML, and Gradle; generate HTML report
// ----------------------------------------------------------------------

func main() {
	// Start BFS concurrency workers
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	fmt.Println("[MAIN] Scanning for pom.xml, .toml, and build.gradle files...")

	// 1) POM files
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	totalPom := 0
	for _, pf := range pomFiles {
		fmt.Printf("[MAIN] Found POM file: %s\n", pf)
		deps, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("[POM] Parse error: %v\n", err)
			continue
		}
		section := doBFSForDirect(deps, pf, "maven")
		pomSections = append(pomSections, section)
		totalPom += len(section.Flattened)
	}

	// 2) TOML files
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	totalToml := 0
	for _, tf := range tomlFiles {
		fmt.Printf("[MAIN] Found TOML file: %s\n", tf)
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

	// 3) Gradle files
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	totalGradle := 0
	for _, gf := range gradleFiles {
		fmt.Printf("[MAIN] Found Gradle file: %s\n", gf)
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

	// Shut down BFS workers
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

	summaryText := fmt.Sprintf("POM total=%d, TOML total=%d, Gradle total=%d, Copyleft=%d", totalPom, totalToml, totalGradle, copyleftCount)

	// Prepare final data for report
	finalData := struct {
		Summary        string
		PomSections    []BFSSection
		TomlSections   []BFSSection
		GradleSections []BFSSection
	}{
		Summary:        summaryText,
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

	outFile, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Printf("[MAIN] Create file error: %v\n", err)
		return
	}
	defer outFile.Close()

	if err := tmpl.Execute(outFile, finalData); err != nil {
		fmt.Printf("[MAIN] Template execute error: %v\n", err)
		return
	}
	fmt.Println("[DONE] license-full-bfs-report.html generated successfully!")
}

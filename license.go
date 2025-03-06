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
// 1) GLOBAL CONFIG + WORKER POOL
// ----------------------------------------------------------------------

const (
	workerCount  = 5
	fetchTimeout = 20 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // concurrency for storing *MavenPOM by G:A:V

	// BFS expansions cache: key = "g:a:v", value = *BFSNode
	bfsExpansions sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// fetch concurrency
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

// Worker routine
func pomWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

// ----------------------------------------------------------------------
// 2) LICENSE DETECTION + SORT
// ----------------------------------------------------------------------

// minimal SPDx map
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":        {Name: "MIT License", Copyleft: false},
	"Apache-2.0": {Name: "Apache License 2.0", Copyleft: false},
	"GPL-3.0":    {Name: "GNU GPL v3.0", Copyleft: true},
}

func isCopyleft(lic string) bool {
	// 1) SPDx direct
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(lic, data.Name) || strings.EqualFold(lic, spdxID)) {
			return true
		}
	}
	// 2) fallback
	keywords := []string{"GPL", "AGPL", "LGPL", "Affero", "MPL", "EPL"}
	up := strings.ToUpper(lic)
	for _, k := range keywords {
		if strings.Contains(up, k) {
			return true
		}
	}
	return false
}

// for final table: copyleft=1, unknown=2, else=3
func getLicenseGroup(lic string) int {
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
}

// ----------------------------------------------------------------------
// 3) MAVEN POM struct + concurrency BFS
// ----------------------------------------------------------------------

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}
type MavenPOM struct {
	GroupID    string
	ArtifactID string
	Version    string
	Licenses []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
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

func detectLicense(m *MavenPOM) string {
	if len(m.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(m.Licenses[0].Name)
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

// concurrency BFS fetch
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		// fallback fetch
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
	return nil, fmt.Errorf("cannot fetch remote POM for %s:%s:%s", g, a, v)
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
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e2 := dec.Decode(&pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

// fallbackVersionIfUnknown => if "unknown" => getLatestVersion
func fallbackVersionIfUnknown(g, a, ver string) (string, error) {
	if strings.ToLower(ver) != "unknown" {
		return ver, nil
	}
	lat, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return lat, nil
}

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
		return "", fmt.Errorf("HTTP %d => %s", resp.StatusCode, url)
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
	return "", fmt.Errorf("no version found in metadata at %s", url)
}

// BFS expansions cache => "g:a:v" => BFSNode pointer
// We'll store the BFS expansions so we don't re-run expansions for the same G:A:V
type BFSNode struct {
	Name     string // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string
	TopLevel string

	Children []*BFSNode
}

func buildFullBFS(g, a, v, parent, top string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, v)
	// cycle detection
	if visited[key] {
		return nil
	}
	visited[key] = true

	// BFS expansions cache
	if cached, ok := bfsExpansions.Load(key); ok {
		// but the BFSNode might have a different parent/top?
		// We'll clone or re-parent it
		orig := cached.(*BFSNode)
		clone := cloneBFSNode(orig)
		clone.Parent = parent
		clone.TopLevel = top
		return clone
	}

	// if "unknown", fallback to latest
	eff, e2 := fallbackVersionIfUnknown(g, a, v)
	pom, err := concurrentFetchPOM(g, a, eff)
	node := &BFSNode{
		Name:   g + "/" + a,
		Version: eff,
		Parent: parent,
		TopLevel: top,
		License: "Unknown",
	}
	if e2 != nil || err != nil || pom == nil {
		// store partial in expansions
		bfsExpansions.Store(key, node)
		return node
	}
	lic := detectLicense(pom)
	node.License = lic
	node.Copyleft = isCopyleft(lic)

	// BFS children
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
		child := buildFullBFS(g2, a2, v2, g+"/"+a+":"+eff, top, visited)
		if child != nil {
			kids = append(kids, child)
		}
	}
	node.Children = kids
	bfsExpansions.Store(key, node)
	return node
}

func cloneBFSNode(orig *BFSNode) *BFSNode {
	n2 := &BFSNode{
		Name: orig.Name,
		Version: orig.Version,
		License: orig.License,
		Copyleft: orig.Copyleft,
		Children: nil, // we will clone children
	}
	// We do NOT copy parent/top from the orig, because BFS expansions might differ
	for _, c := range orig.Children {
		cc := cloneBFSNode(c)
		n2.Children = append(n2.Children, cc)
	}
	return n2
}

// expansions => <details>
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
	Language string

	RepoInfo string
}

func flattenBFSNode(n *BFSNode, lang string, out *[]FlatDep) {
	if n == nil {
		return
	}
	g, a := splitGA(n.Name)
	repo := buildRepoLink(g, a, n.Version)
	fd := FlatDep{
		Name:     n.Name,
		Version:  n.Version,
		License:  n.License,
		Parent:   n.Parent,
		TopLevel: n.TopLevel,
		Copyleft: n.Copyleft,
		Language: lang,
		RepoInfo: repo,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFSNode(c, lang, out)
	}
}

func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" {
		q := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s",
		a, g, a, v)
}

func splitGA(ga string) (string, string) {
	p := strings.SplitN(ga, "/", 2)
	if len(p) != 2 {
		return "", ""
	}
	return p[0], p[1]
}

// BFS expansions for direct dependencies
type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// doBFSForDirect => for each direct G/A => BFS expansions => flatten
func doBFSForDirect(depMap map[string]string, topFile, lang string) BFSSection {
	visited := make(map[string]bool)
	var roots []*BFSNode
	for ga, ver := range depMap {
		g, a := splitGA(ga)
		node := buildFullBFS(g, a, ver, "direct", ga, visited)
		if node != nil {
			roots = append(roots, node)
		}
	}
	var flat []FlatDep
	for _, r := range roots {
		flattenBFSNode(r, lang, &flat)
	}
	// sort
	sort.SliceStable(flat, func(i, j int) bool {
		gi := getLicenseGroup(flat[i].License)
		gj := getLicenseGroup(flat[j].License)
		return gi < gj
	})
	return BFSSection{
		FilePath:  topFile,
		BFSNodes:  roots,
		Flattened: flat,
	}
}

// ----------------------------------------------------------------------
// 4) PARSE + BFS expansions for POM, TOML, Gradle
// ----------------------------------------------------------------------

func findAllPOMFiles(root string) ([]string, error) {
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
func parseOnePomFile(filePath string) (map[string]string, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	xml.Unmarshal(dat, &pom)
	res := make(map[string]string)
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
	return res, nil
}

func findTOMLFile(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}
func parseOneTomlFile(filePath string) (map[string]string, error) {
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, err
	}
	libObj := tree.Get("libraries")
	if libObj == nil {
		return nil, nil
	}
	libTree, ok := libObj.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", filePath)
	}
	res := make(map[string]string)
	for _, k := range libTree.Keys() {
		val := libTree.Get(k)
		sub, ok2 := val.(*toml.Tree)
		if !ok2 {
			continue
		}
		modStr, _ := sub.Get("module").(string)
		verRef, _ := sub.Get("version.ref").(string)
		if modStr == "" || verRef == "" {
			continue
		}
		parts := strings.SplitN(modStr, ":", 2)
		if len(parts) != 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		key := g + "/" + a
		res[key] = verRef
	}
	return res, nil
}

func findBuildGradleFiles(root string) ([]string, error) {
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
func parseOneGradleFile(filePath string) (map[string]string, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(dat)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	res := make(map[string]string)
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
		key := g + "/" + a
		res[key] = v
	}
	return res, nil
}

// ----------------------------------------------------------------------
// 5) FINAL HTML
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
<h1>Full BFS License Report (with caching)</h1>
<h2>Summary</h2>
<p>{{.Summary}}</p>

<h2>POM Results</h2>
{{range .PomSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this file.</p>
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
<hr/>
{{end}}
{{end}}

<h2>TOML Results</h2>
{{range .TomlSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this file.</p>
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
<hr/>
{{end}}
{{end}}

<h2>Gradle Results</h2>
{{range .GradleSections}}
<h3>File: {{.FilePath}}</h3>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in this file.</p>
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
<hr/>
{{end}}
{{end}}

</body>
</html>
`

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

func buildBFSHTMLFunc(n *BFSNode) template.HTML {
	return template.HTML(buildBFSHTML(n))
}

func main() {
	// 1) start concurrency
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// 2) parse poms
	pomFiles, _ := findAllPOMFiles(".")
	var pomSecs []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		depMap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("Error parse POM => %s: %v\n", pf, err)
			continue
		}
		sec := doBFSForDirect(depMap, pf, "maven")
		pomSecs = append(pomSecs, sec)
		totalPom += len(sec.Flattened)
	}

	// 3) parse tomls
	tomlFiles, _ := findTOMLFile(".")
	var tomlSecs []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		depMap, err := parseOneTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML => %s: %v\n", tf, err)
			continue
		}
		sec := doBFSForDirect(depMap, tf, "toml")
		tomlSecs = append(tomlSecs, sec)
		totalToml += len(sec.Flattened)
	}

	// 4) parse gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSecs []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		depMap, err := parseOneGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle => %s: %v\n", gf, err)
			continue
		}
		sec := doBFSForDirect(depMap, gf, "gradle")
		gradleSecs = append(gradleSecs, sec)
		totalGradle += len(sec.Flattened)
	}

	// close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// count copyleft
	copyleftCount := 0
	for _, s := range pomSecs {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range tomlSecs {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range gradleSecs {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d",
		totalPom, totalToml, totalGradle, copyleftCount)

	data := struct {
		Summary       string
		PomSections   []BFSSection
		TomlSections  []BFSSection
		GradleSections []BFSSection
	}{
		Summary: summary,
		PomSections: pomSecs,
		TomlSections: tomlSecs,
		GradleSections: gradleSecs,
	}

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"isCopyleft":   isCopyleft,
		"buildBFSHTML": buildBFSHTMLFunc,
	}).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error =>", err)
		return
	}
	out, err2 := os.Create("license-full-bfs-report.html")
	if err2 != nil {
		fmt.Println("Create file error =>", err2)
		return
	}
	defer out.Close()

	if e3 := tmpl.Execute(out, data); e3 != nil {
		fmt.Println("Template exec error =>", e3)
		return
	}
	fmt.Println("license-full-bfs-report.html generated successfully with BFS caching!")
}

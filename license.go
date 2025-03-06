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

// 1) GLOBALS / CONFIG
const (
	workerCount  = 5
	fetchTimeout = 30 * time.Second
)

var (
	// concurrency BFS for remote POM
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup

	// Caches
	pomCache sync.Map // key="group:artifact:version" => *MavenPOM

	channelOpen  = true
	channelMutex sync.Mutex
)

// 2) BASIC COPYLEFT DETECTION
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":                              {Name: "MIT License", Copyleft: false},
	"Apache-2.0":                       {Name: "Apache License 2.0", Copyleft: false},
	"BSD-2-CLAUSE":                     {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-CLAUSE":                     {Name: "BSD 3-Clause", Copyleft: false},
	"GPL":                              {Name: "GNU General Public License", Copyleft: true},
	"GNU GENERAL PUBLIC LICENSE":       {Name: "GNU General Public License", Copyleft: true},
	"LGPL":                             {Name: "GNU Lesser General Public License", Copyleft: true},
	"GNU LESSER GENERAL PUBLIC LICENSE": {Name: "GNU Lesser General Public License", Copyleft: true},
	"AGPL":                             {Name: "GNU Affero General Public License", Copyleft: true},
	"GNU AFFERO GENERAL PUBLIC LICENSE": {Name: "GNU Affero General Public License", Copyleft: true},
	"MPL":                              {Name: "Mozilla Public License", Copyleft: true},
	"MOZILLA PUBLIC LICENSE":           {Name: "Mozilla Public License", Copyleft: true},
	"CC-BY-SA":                         {Name: "Creative Commons Attribution-ShareAlike", Copyleft: true},
	"EPL":                              {Name: "Eclipse Public License", Copyleft: true},
	"OFL":                              {Name: "Open Font License", Copyleft: true},
	"CPL":                              {Name: "Common Public License", Copyleft: true},
	"OSL":                              {Name: "Open Software License", Copyleft: true},
	"CDDL":                             {Name: "Common Development and Distribution License", Copyleft: true},
	"EUPL":                             {Name: "European Union Public License", Copyleft: true},
}

func isCopyleft(license string) bool {
	// 1) Check SPDx table
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	// 2) fallback keywords
	fallbackKeywords := []string{
		"GPL", "GNU GENERAL PUBLIC LICENSE",
		"LGPL", "GNU LESSER GENERAL PUBLIC LICENSE",
		"AGPL", "GNU AFFERO GENERAL PUBLIC LICENSE",
		"MPL", "MOZILLA PUBLIC LICENSE",
		"CC-BY-SA", "CREATIVE COMMONS ATTRIBUTION-SHAREALIKE",
		"EPL", "ECLIPSE PUBLIC LICENSE",
		"OFL", "OPEN FONT LICENSE",
		"CPL", "COMMON PUBLIC LICENSE",
		"OSL", "OPEN SOFTWARE LICENSE",
		"CDDL", "COMMON DEVELOPMENT AND DISTRIBUTION LICENSE",
		"EUPL", "EUROPEAN UNION PUBLIC LICENSE",
	}
	up := strings.ToUpper(license)
	for _, kw := range fallbackKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

func getLicenseGroup(lic string) int {
	if isCopyleft(lic) {
		return 1
	} else if strings.EqualFold(lic, "unknown") {
		return 2
	}
	return 3
}

// 3) POM FETCH WORKER
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

// 4) skipScope => skip test/provided/system & optional
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

// 5) MAVEN POM STRUCT
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

// 6) concurrency BFS
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

// 7) fetchRemotePOM => tries maven central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		return pm, nil
	}
	if pm2, e2 := fetchPOMFromURL(urlG); e2 == nil && pm2 != nil {
		return pm2, nil
	}
	return nil, fmt.Errorf("unable to fetch POM for %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d => %s", resp.StatusCode, url)
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

// 8) fallbackVersionIfUnknown => if "unknown" => getLatestVersion
func fallbackVersionIfUnknown(g, a, ver string) (string, error) {
	if strings.ToLower(ver) != "unknown" {
		return ver, nil
	}
	latest, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return latest, nil
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
	client := http.Client{Timeout: 15 * time.Second}
	resp, err := client.Get(url)
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
	if e := xml.Unmarshal(dat, &md); e != nil {
		return "", e
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
	return "", fmt.Errorf("no version found in %s", url)
}

// 9) Utility => splitGA, buildRepoLink
func splitGA(ga string) (string, string) {
	arr := strings.SplitN(ga, "/", 2)
	if len(arr) != 2 {
		return "", ""
	}
	return arr[0], arr[1]
}

func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" {
		qq := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(qq, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, v)
}

// 10) BFS Node => unlimited BFS
type BFSNode struct {
	Name     string // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string
	TopLevel string

	Children []*BFSNode
}

func buildFullBFS(g, a, ver, parent, top string, visited map[string]bool) *BFSNode {
	key := g + "/" + a + "@" + ver
	if visited[key] {
		return nil
	}
	visited[key] = true

	// fallback version if unknown
	eff, e2 := fallbackVersionIfUnknown(g, a, ver)
	if e2 != nil {
		eff = ver
	}
	// create BFS node
	node := &BFSNode{
		Name:    g + "/" + a,
		Version: eff,
		Parent:  parent,
		TopLevel: top,
		License: "Unknown",
	}
	pom, err := concurrentFetchPOM(g, a, eff)
	if err == nil && pom != nil {
		// detect license
		lic := detectLicense(pom)
		node.License = lic
		node.Copyleft = isCopyleft(lic)
		// children BFS
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
				node.Children = append(node.Children, child)
			}
		}
	}
	return node
}

func buildBFSHTML(n *BFSNode) string {
	if n == nil {
		return ""
	}
	sum := fmt.Sprintf("%s@%s (License: %s)", n.Name, n.Version, n.License)
	css := "non-copyleft"
	if n.License == "Unknown" {
		css = "unknown"
	} else if n.Copyleft {
		css = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details><summary class=\"" + css + "\">")
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
		TopLevel: n.TopLevel,
		Copyleft: n.Copyleft,
		Language: lang,
		RepoInfo: link,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFSNode(c, lang, out)
	}
}

// 11) BFSSection + FlatDep
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

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// doBFSForDirect => for direct dependencies => BFS expansions
func doBFSForDirect(depMap map[string]string, filePath, lang string) BFSSection {
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

// 12) PARSE: POM, TOML, Gradle

// POM
func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
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
	if e2 := xml.Unmarshal(dat, &pom); e2 != nil {
		return nil, e2
	}
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

// TOML
func findTOMLFile(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
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
		return nil, fmt.Errorf("'libraries' is not valid in %s", filePath)
	}
	res := make(map[string]string)
	for _, k := range libTree.Keys() {
		subVal := libTree.Get(k)
		sub, ok2 := subVal.(*toml.Tree)
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

// Gradle
func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e == nil && !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
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
		parts := strings.Split(coord, ":")
		if len(parts) < 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		v := "unknown"
		if len(parts) >= 3 {
			v = parts[2]
		}
		key := g + "/" + a
		res[key] = v
	}
	return res, nil
}

// 13) finalData for the HTML, BFSSection for each file type
type finalData struct {
	Summary        string
	PomSections    []BFSSection
	TomlSections   []BFSSection
	GradleSections []BFSSection
}

// 14) The HTML Template
var finalTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>License BFS Full Report</title>
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
      <th>Top-Level</th>
      <th>Language</th>
      <th>Maven/Repo Info</th>
    </tr>
    {{range .Flattened}}
    <tr>
      <td>{{.Name}}</td>
      <td>{{.Version}}</td>
      <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
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
      <th>Top-Level</th>
      <th>Language</th>
      <th>Maven/Repo Info</th>
    </tr>
    {{range .Flattened}}
    <tr>
      <td>{{.Name}}</td>
      <td>{{.Version}}</td>
      <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
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
      <th>Top-Level</th>
      <th>Language</th>
      <th>Maven/Repo Info</th>
    </tr>
    {{range .Flattened}}
    <tr>
      <td>{{.Name}}</td>
      <td>{{.Version}}</td>
      <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
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

// 15) MAIN
func main() {
	// spawn concurrency workers
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		dmap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("Error parsing POM file %s => %v\n", pf, err)
			continue
		}
		psec := doBFSForDirect(dmap, pf, "maven")
		pomSections = append(pomSections, psec)
		totalPom += len(psec.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFile(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		dmap, err := parseOneTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parsing TOML file %s => %v\n", tf, err)
			continue
		}
		if dmap == nil {
			continue
		}
		tsec := doBFSForDirect(dmap, tf, "toml")
		tomlSections = append(tomlSections, tsec)
		totalToml += len(tsec.Flattened)
	}

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		dmap, err := parseOneGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle file %s => %v\n", gf, err)
			continue
		}
		gsec := doBFSForDirect(dmap, gf, "gradle")
		gradleSections = append(gradleSections, gsec)
		totalGradle += len(gsec.Flattened)
	}

	// close concurrency BFS
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// count copyleft
	copyleftCount := 0
	for _, s := range pomSections {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range tomlSections {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range gradleSections {
		for _, f := range s.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d", totalPom, totalToml, totalGradle, copyleftCount)
	finalData := struct {
		Summary        string
		PomSections    []BFSSection
		TomlSections   []BFSSection
		GradleSections []BFSSection
	}{
		summary,
		pomSections,
		tomlSections,
		gradleSections,
	}

	funcMap := template.FuncMap{
		"isCopyleft":   isCopyleft,
		"buildBFSHTML": func(n *BFSNode) template.HTML {
			return template.HTML(buildBFSHTML(n))
		},
	}
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error:", err)
		return
	}
	out, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Println("Error creating output file =>", err)
		return
	}
	defer out.Close()

	if err := tmpl.Execute(out, finalData); err != nil {
		fmt.Println("Template exec error =>", err)
		return
	}

	fmt.Println("license-full-bfs-report.html generated successfully!")
}

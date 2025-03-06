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
// 1) GLOBAL CONFIG & WORKER POOL
// ----------------------------------------------------------------------

const (
	workerCount  = 5
	fetchTimeout = 30 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key => "group:artifact:version" => *MavenPOM

	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) LICENSE DETECTION (Comprehensive copyleft from your code)
// ----------------------------------------------------------------------

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
	// 1) SPDx direct
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	// 2) fallback keywords (AGPL, GPL, etc.)
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

func getLicenseGroup(license string) int {
	if isCopyleft(license) {
		return 1
	} else if strings.EqualFold(license, "unknown") {
		return 2
	}
	return 3
}

// ----------------------------------------------------------------------
// 3) SKIP SCOPE => skip test/provided/system or optional
// ----------------------------------------------------------------------

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

// ----------------------------------------------------------------------
// 4) BFS WORKER FOR concurrency
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

// ----------------------------------------------------------------------
// 5) MAVEN POM struct + detectLicense
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

// ----------------------------------------------------------------------
// 6) concurrency BFS fetch => concurrentFetchPOM
// ----------------------------------------------------------------------

func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	// cache check
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	// concurrency check
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()

	if !open {
		// direct fetch
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	rq := fetchRequest{g, a, v, make(chan fetchResult, 1)}
	pomRequests <- rq
	res := <-rq.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// fetchRemotePOM => tries central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	u1 := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	u2 := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)

	if pm, e := fetchPOMFromURL(u1); e == nil && pm != nil {
		return pm, nil
	}
	if pm2, e2 := fetchPOMFromURL(u2); e2 == nil && pm2 != nil {
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

// ----------------------------------------------------------------------
// 7) fallbackVersionIfUnknown => getLatestVersion
// ----------------------------------------------------------------------

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
	uCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, e := fetchLatestVersionFromURL(uCentral); e == nil && v != "" {
		return v, nil
	}
	uGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v2, e2 := fetchLatestVersionFromURL(uGoogle); e2 == nil && v2 != "" {
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
	return "", fmt.Errorf("no version found in %s", url)
}

// ----------------------------------------------------------------------
// 8) UTILS: splitGA, buildRepoLink with improved logic
// ----------------------------------------------------------------------

func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// buildRepoLink => tries to guess a better link than always Google Maven
// If group starts "androidx." or "com.android" => google's maven
// If group has "jetbrains" or "kotlin" => search.maven.org
// else => search.maven.org fallback
// if group/artifact empty => google search
func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" {
		q := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	if strings.HasPrefix(g, "com.android") || strings.HasPrefix(g, "androidx") {
		return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, v)
	}
	if strings.Contains(g, "jetbrains") || strings.Contains(g, "kotlin") {
		return fmt.Sprintf("https://search.maven.org/artifact/%s/%s/%s/pom", g, a, v)
	}
	// fallback => search.maven.org
	return fmt.Sprintf("https://search.maven.org/artifact/%s/%s/%s/pom", g, a, v)
}

// ----------------------------------------------------------------------
// 9) BFS Node (unlimited) for POM/TOML/Gradle expansions
// ----------------------------------------------------------------------

type BFSNode struct {
	Name     string // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string // "direct" or "g/a@v"
	Children []*BFSNode
}

func buildFullBFS(g, a, ver, parent string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, ver)
	if visited[key] {
		return nil
	}
	visited[key] = true

	// fallback
	eff, e2 := fallbackVersionIfUnknown(g, a, ver)
	if e2 != nil {
		eff = ver
	}
	n := &BFSNode{
		Name:   g + "/" + a,
		Version: eff,
		Parent: parent,
		License: "Unknown",
	}
	pom, fe := concurrentFetchPOM(g, a, eff)
	if fe == nil && pom != nil {
		lic := detectLicense(pom)
		n.License  = lic
		n.Copyleft = isCopyleft(lic)
		for _, d := range pom.Dependencies {
			if skipScope(d.Scope, d.Optional) {
				continue
			}
			cg := d.GroupID
			ca := d.ArtifactID
			cv := d.Version
			if cv == "" {
				cv = "unknown"
			}
			child := buildFullBFS(cg, ca, cv, n.Name+"@"+eff, visited)
			if child != nil {
				n.Children = append(n.Children, child)
			}
		}
	}
	return n
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
		RepoInfo: link,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFSNode(c, lang, out)
	}
}

// flattened table
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoInfo string
}

// BFSSection => each file => BFS expansions
type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

// BFS from direct map
func doBFSForDirect(deps map[string]string, filePath, lang string) BFSSection {
	visited := make(map[string]bool)
	var roots []*BFSNode
	for ga, ver := range deps {
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
	// sort copyleft first => unknown => others
	sort.SliceStable(flat, func(i, j int) bool {
		return getLicenseGroup(flat[i].License) < getLicenseGroup(flat[j].License)
	})
	return BFSSection{filePath, roots, flat}
}

// ----------------------------------------------------------------------
// 10) FILE PARSING: POM, TOML, GRADLE
// ----------------------------------------------------------------------

// parse POM
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

// parse .toml
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
	libObj := tree.Get("libraries")
	if libObj == nil {
		return deps, nil
	}
	libTree, ok := libObj.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not valid in %s", filePath)
	}
	for _, k := range libTree.Keys() {
		v := libTree.Get(k)
		sub, ok2 := v.(*toml.Tree)
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
		g := parts[0]
		a := parts[1]
		key := g + "/" + a
		deps[key] = verRef
	}
	return deps, nil
}

// parse build.gradle
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
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(dat)
	res := make(map[string]string)
	varMap := parseGradleVars(content)

	rx := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := rx.FindAllStringSubmatch(content, -1)
	for _, mm := range matches {
		coord := mm[2]
		pp := strings.Split(coord, ":")
		if len(pp) < 2 {
			continue
		}
		g := pp[0]
		a := pp[1]
		v := "unknown"
		if len(pp) >= 3 {
			v = pp[2]
			if strings.Contains(v, "${") {
				reVar := regexp.MustCompile(`\$\{([^}]+)\}`)
				v = reVar.ReplaceAllStringFunc(v, func(s string) string {
					inner := s[2 : len(s)-1]
					if val, ok := varMap[inner]; ok {
						return val
					}
					return ""
				})
				if v == "" {
					v = "unknown"
				}
			}
		}
		key := g + "/" + a
		res[key] = v
	}
	return res, nil
}
func parseGradleVars(content string) map[string]string {
	out := make(map[string]string)
	rx := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := rx.FindAllStringSubmatch(content, -1)
	for _, mm := range matches {
		out[mm[1]] = mm[2]
	}
	return out
}

// ----------------------------------------------------------------------
// 11) FINAL HTML
// ----------------------------------------------------------------------

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
body { font-family: Arial,sans-serif; margin:20px; }
h1,h2 { color:#2c3e50; }
table { width:100%; border-collapse:collapse; margin-bottom:20px; }
th,td { border:1px solid #ddd; padding:8px; text-align:left; }
th { background:#f2f2f2; }
.copyleft { background:#f8d7da; color:#721c24; }
.unknown { background:#ffff99; color:#333; }
.non-copyleft { background:#d4edda; color:#155724; }
details { margin:4px 0; }
summary { cursor:pointer; font-weight:bold; }
</style>
</head>
<body>
<h1>License Full BFS Report</h1>
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
      <th>Maven/Repo Info</th>
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
      <th>Maven/Repo Info</th>
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
      <th>Maven/Repo Info</th>
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

// BFS expansions => <details> block
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

// ----------------------------------------------------------------------
// 12) MAIN
// ----------------------------------------------------------------------

func main() {
	// Start concurrency BFS
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
			fmt.Printf("Error parse POM => %s => %v\n", pf, err)
			continue
		}
		sec := doBFSForDirect(dmap, pf, "maven")
		pomSections = append(pomSections, sec)
		totalPom += len(sec.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		deps, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML => %s => %v\n", tf, err)
			continue
		}
		if len(deps) == 0 {
			continue
		}
		sec := doBFSForDirect(deps, tf, "toml")
		tomlSections = append(tomlSections, sec)
		totalToml += len(sec.Flattened)
	}

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		deps, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle => %s => %v\n", gf, err)
			continue
		}
		if len(deps) == 0 {
			continue
		}
		sec := doBFSForDirect(deps, gf, "gradle")
		gradleSections = append(gradleSections, sec)
		totalGradle += len(sec.Flattened)
	}

	// close concurrency BFS
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Count copyleft
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

	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d",
		totalPom, totalToml, totalGradle, copyleftCount)

	// Prepare final data
	data := finalData{
		Summary:        summary,
		PomSections:    pomSections,
		TomlSections:   tomlSections,
		GradleSections: gradleSections,
	}

	// Render final HTML
	funcMap := template.FuncMap{
		"isCopyleft": isCopyleft,
		"buildBFSHTML": func(n *BFSNode) template.HTML {
			return template.HTML(buildBFSHTML(n))
		},
	}
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
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

	fmt.Println("license-full-bfs-report.html generated successfully!")
}

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
// 2) LICENSE DETECTION: same copyleft approach from your original code
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

func isCopyleft(lic string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(lic, data.Name) ||
			strings.EqualFold(lic, spdxID)) {
			return true
		}
	}
	// fallback keywords
	keywords := []string{
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
	up := strings.ToUpper(lic)
	for _, kw := range keywords {
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

// ----------------------------------------------------------------------
// 3) skipScope => skip test/provided/system or optional
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
// 4) BFS Worker concurrency
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
// 5) MAVEN POM struct, detectLicense
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

func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(pom.Licenses[0].Name)
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
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		// direct fetch
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

// fetchRemotePOM => tries central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)

	if p, e := fetchPOMFromURL(urlC); e == nil && p != nil {
		return p, nil
	}
	if p2, e2 := fetchPOMFromURL(urlG); e2 == nil && p2 != nil {
		return p2, nil
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
	latest, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return latest, nil
}

func getLatestVersion(g, a string) (string, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	u1 := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", gpath, a)
	if v, e := fetchLatestVersionFromURL(u1); e == nil && v != "" {
		return v, nil
	}
	u2 := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", gpath, a)
	if v2, e2 := fetchLatestVersionFromURL(u2); e2 == nil && v2 != "" {
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
// 8) UTILS: splitGA, buildRepoLink => small enhancement for link
// ----------------------------------------------------------------------

func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// If group starts with "androidx." or "com.android." => google maven
// if group contains "jetbrains" or "kotlin" => search.maven.org
// else => search.maven.org fallback
// if group or artifact is empty => google search
func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" {
		qq := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(qq, " ", "+")
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
// 9) BFS Node expansions
// ----------------------------------------------------------------------

type BFSNode struct {
	Name     string
	Version  string
	License  string
	Copyleft bool
	Parent   string
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
	node := &BFSNode{
		Name:   g + "/" + a,
		Version: eff,
		Parent: parent,
		License: "Unknown",
	}
	pom, ferr := concurrentFetchPOM(g, a, eff)
	if ferr == nil && pom != nil {
		lic := detectLicense(pom)
		node.License  = lic
		node.Copyleft = isCopyleft(lic)
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
			child := buildFullBFS(cg, ca, cv, node.Name+"@"+eff, visited)
			if child != nil {
				node.Children = append(node.Children, child)
			}
		}
	}
	return node
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

// Flatten BFS => for the final table
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Parent   string
	Copyleft bool
	Language string
	RepoInfo string
}

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
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
		return getLicenseGroup(flat[i].License) < getLicenseGroup(flat[j].License)
	})
	return BFSSection{
		FilePath:  filePath,
		BFSNodes:  roots,
		Flattened: flat,
	}
}

// ----------------------------------------------------------------------
// 10) PARSING: pom.xml, .toml, build.gradle
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
	deps := make(map[string]string)
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
		deps[key] = v
	}
	return deps, nil
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
	res := make(map[string]string)
	libObj := tree.Get("libraries")
	if libObj == nil {
		return res, nil
	}
	libTree, ok := libObj.(*toml.Tree)
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
		key := g + "/" + a
		res[key] = verRef
	}
	return res, nil
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
	rv := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := rv.FindAllStringSubmatch(content, -1)
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
	// Start BFS concurrency
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// 1) find & parse POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		depMap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("Error parse POM => %s => %v\n", pf, err)
			continue
		}
		sec := doBFSForDirect(depMap, pf, "maven")
		pomSections = append(pomSections, sec)
		totalPom += len(sec.Flattened)
	}

	// 2) find & parse TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		dMap, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML => %s => %v\n", tf, err)
			continue
		}
		if len(dMap) == 0 {
			continue
		}
		ts := doBFSForDirect(dMap, tf, "toml")
		tomlSections = append(tomlSections, ts)
		totalToml += len(ts.Flattened)
	}

	// 3) find & parse Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		gMap, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle => %s => %v\n", gf, err)
			continue
		}
		if len(gMap) == 0 {
			continue
		}
		gs := doBFSForDirect(gMap, gf, "gradle")
		gradleSections = append(gradleSections, gs)
		totalGradle += len(gs.Flattened)
	}

	// close BFS concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// count copyleft
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

	// final data
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
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error:", err)
		return
	}
	out, err2 := os.Create("license-full-bfs-report.html")
	if err2 != nil {
		fmt.Println("Create file error:", err2)
		return
	}
	defer out.Close()

	if e3 := tmpl.Execute(out, data); e3 != nil {
		fmt.Println("Template exec error:", e3)
		return
	}

	fmt.Println("license-full-bfs-report.html generated successfully!")
}

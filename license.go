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
	localPOMCacheDir = ".pom-cache"
	pomWorkerCount   = 10
	fetchTimeout     = 30 * time.Second
)

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect parent cycles in parent POM resolution

	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) LICENSE DETECTION (same as license(1).go + expansions)
// ----------------------------------------------------------------------

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
	// First check direct spdx
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) ||
			strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// fallback
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "MPL", "EPL", "CPL",
		"CDDL", "EUPL", "Affero", "OSL", "CeCILL",
		"GNU General Public License",
		"GNU Lesser General Public License",
		"Mozilla Public License",
		"Common Development and Distribution License",
		"Eclipse Public License",
		"Common Public License",
		"European Union Public License",
		"Open Software License",
	}
	up := strings.ToUpper(name)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// ----------------------------------------------------------------------
// 3) skipScope => test / provided / system / optional
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
// 4) BFS concurrency
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

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("[Worker] Attempt fetch => %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

// ----------------------------------------------------------------------
// 5) MAVEN POM struct + local disk caching + detectLicense
// ----------------------------------------------------------------------

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

	// We can store parent references if needed
}

// detectLicense => from the first license
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
// 6) retrieveOrLoadPOM => tries local disk, else fetch remote, store disk
//    (like license(1).go approach)
// ----------------------------------------------------------------------

func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	fmt.Printf("[retrieveOrLoadPOM] Checking local disk for %s\n", key)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("[retrieveOrLoadPOM] Cache HIT in-memory => %s\n", key)
		return c.(*MavenPOM), nil
	}
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
		fmt.Printf("[retrieveOrLoadPOM] Found local disk POM => %s\n", key)
		return pom, nil
	}
	fmt.Printf("[retrieveOrLoadPOM] Not on disk => must fetch => %s\n", key)
	remote, e2 := fetchRemotePOM(g, a, v)
	if e2 != nil {
		return nil, e2
	}
	pomCache.Store(key, remote)
	savePOMToDisk(g, a, v, remote)
	return remote, nil
}

// load from local disk
func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	fmt.Printf("   Found local disk => %s\n", path)
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e2 := dec.Decode(&pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

func savePOMToDisk(g, a, v string, pom *MavenPOM) {
	path := localCachePath(g, a, v)
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		fmt.Printf("Error making dirs => %v\n", err)
		return
	}
	out, err := os.Create(path)
	if err != nil {
		fmt.Printf("Error create local pom => %v\n", err)
		return
	}
	defer out.Close()
	data, e2 := xml.MarshalIndent(pom, "", "  ")
	if e2 != nil {
		fmt.Printf("Error marshal => %v\n", e2)
		return
	}
	out.Write(data)
	fmt.Printf("   Saved POM to disk => %s\n", path)
}

func localCachePath(g, a, v string) string {
	gpath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, gpath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// fetchRemotePOM => tries central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	gpath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", gpath, a, v, a, v)
	fmt.Printf("   [fetchRemotePOM] Try central => %s\n", urlC)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		return pm, nil
	}
	fmt.Printf("   [fetchRemotePOM] Try google => %s\n", urlG)
	if pm2, e2 := fetchPOMFromURL(urlG); e2 == nil && pm2 != nil {
		return pm2, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM => %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	fmt.Printf("      => GET %s\n", url)
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

// ----------------------------------------------------------------------
// 9) BFS Node expansions
// ----------------------------------------------------------------------

type BFSNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*BFSNode
}

func buildFullBFS(g, a, ver, parent string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, ver)
	if visited[key] {
		return nil
	}
	visited[key] = true

	// If version="unknown", skip BFS expansions
	if strings.ToLower(ver) == "unknown" {
		fmt.Printf("[BFS] version unknown => skip sub fetch => %s/%s\n", g, a)
		return &BFSNode{
			Name:    g + "/" + a,
			Version: ver,
			License: "Unknown",
			Parent:  parent,
		}
	}
	fmt.Printf("[BFS] Attempt => %s/%s@%s (parent=%s)\n", g, a, ver, parent)

	// retrieve
	pom, err := retrieveOrLoadPOM(g, a, ver)
	node := &BFSNode{
		Name:    g + "/" + a,
		Version: ver,
		Parent:  parent,
		License: "Unknown",
	}
	if err != nil || pom == nil {
		fmt.Printf("[BFS] fetch error => %v => set Unknown for %s\n", err, key)
		return node
	}
	// parse license
	lic := detectLicense(pom)
	node.License = lic
	node.Copyleft = isCopyleft(lic)

	// sub BFS
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			fmt.Printf("   skip scope => %s:%s => %s optional=%s\n",
				d.GroupID, d.ArtifactID, d.Scope, d.Optional)
			continue
		}
		cg := d.GroupID
		ca := d.ArtifactID
		cv := d.Version
		if cv == "" {
			cv = "unknown"
		}
		child := buildFullBFS(cg, ca, cv, g+"/"+a+":"+ver, visited)
		if child != nil {
			node.Transitive = append(node.Transitive, child)
		}
	}
	return node
}

// Flatten BFS for the table
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
		// We might build a link logic or just do a google search
		// or keep it simpler (like license(1).go). We'll do a google search
		RepoInfo: fmt.Sprintf("https://www.google.com/search?q=%s+version+%s", n.Name, n.Version),
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenBFSNode(c, lang, out)
	}
}

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

// BFS from direct
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
// 10) PARSE: pom.xml, .toml, build.gradle (top-level scanning)
// ----------------------------------------------------------------------

// POM
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
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	if e := xml.Unmarshal(data, &pom); e != nil {
		return nil, e
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
	libs := tree.Get("libraries")
	if libs == nil {
		return res, nil
	}
	libTree, ok := libs.(*toml.Tree)
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
		parts := strings.Split(mod, ":")
		if len(parts) != 2 {
			continue
		}
		g, a := parts[0], parts[1]
		res[g+"/"+a] = verRef
	}
	return res, nil
}

// Gradle
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
<h1>Full BFS License Report (with .pom-cache & debugging)</h1>
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
  <th>Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Search</a></td>
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
  <th>Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Search</a></td>
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
  <th>Info</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">{{.License}}</td>
  <td>{{.Parent}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfo}}" target="_blank">Search</a></td>
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
// 12) MAIN
// ----------------------------------------------------------------------

func main() {
	// concurrency
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	fmt.Println("[MAIN] Searching for POM, TOML, Gradle files...")

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		fmt.Printf("Found POM => %s\n", pf)
		deps, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("   parseOnePomFile error => %v\n", err)
			continue
		}
		sec := doBFSForDirect(deps, pf, "maven")
		pomSections = append(pomSections, sec)
		totalPom += len(sec.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFiles(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		fmt.Printf("Found TOML => %s\n", tf)
		deps, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("   parseTomlFile error => %v\n", err)
			continue
		}
		if len(deps) == 0 {
			fmt.Printf("   no libraries found => %s\n", tf)
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
		fmt.Printf("Found Gradle => %s\n", gf)
		deps, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("   parseBuildGradleFile => %v\n", err)
			continue
		}
		if len(deps) == 0 {
			fmt.Printf("   no gradle deps => %s\n", gf)
			continue
		}
		sec := doBFSForDirect(deps, gf, "gradle")
		gradleSections = append(gradleSections, sec)
		totalGradle += len(sec.Flattened)
	}

	// close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// final counts
	copyleftCount := 0
	for _, s := range pomSections {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range tomlSections {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range gradleSections {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d",
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
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Printf("Template parse error => %v\n", err)
		return
	}
	out, e2 := os.Create("license-full-bfs-report.html")
	if e2 != nil {
		fmt.Printf("Create file => %v\n", e2)
		return
	}
	defer out.Close()

	if e3 := tmpl.Execute(out, data); e3 != nil {
		fmt.Printf("Template exec => %v\n", e3)
		return
	}

	fmt.Println("[DONE] license-full-bfs-report.html generated with BFS expansions + local .pom-cache approach!")
}

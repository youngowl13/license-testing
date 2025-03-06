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
// 1) GLOBALS / CONFIG
// ----------------------------------------------------------------------

const (
	workerCount  = 5
	fetchTimeout = 30 * time.Second // for each remote .pom fetch
)

var (
	pomRequests  = make(chan fetchRequest, 50) // concurrency channel
	wgWorkers    sync.WaitGroup

	// POM cache: key => "group:artifact:version"
	pomCache sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) LICENSE DETECTION (Comprehensive copyleft set)
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
	// 1) Check SPDx map
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	// 2) Additional fallback keywords
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

// ----------------------------------------------------------------------
// 3) skipScope => skip test/provided/system & optional="true"
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
// 4) BFS WORKER (fetch .pom concurrently)
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
// 5) MAVEN POM STRUCT + DETECT LICENSE
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
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		// channel closed => direct fetch
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
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
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

// ----------------------------------------------------------------------
// 7) If version=unknown => fallback to getLatestVersion
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
	data, err := io.ReadAll(resp.Body)
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
	if e2 := xml.Unmarshal(data, &md); e2 != nil {
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
// 8) BFS NODE for final expansions
// ----------------------------------------------------------------------

type BFSNode struct {
	Name     string // "group/artifact"
	Version  string
	License  string
	Copyleft bool
	Parent   string // e.g. "direct" or "g/a@v"
	Children []*BFSNode
}

// buildFullBFS => unlimited BFS
func buildFullBFS(g, a, ver, parent, top string, visited map[string]bool) *BFSNode {
	key := fmt.Sprintf("%s/%s@%s", g, a, ver)
	if visited[key] {
		return nil
	}
	visited[key] = true

	eff, errFallback := fallbackVersionIfUnknown(g, a, ver)
	if errFallback != nil {
		eff = ver
	}
	node := &BFSNode{
		Name:    g + "/" + a,
		Version: eff,
		Parent:  parent,
		License: "Unknown",
	}
	pom, err := concurrentFetchPOM(g, a, eff)
	if err == nil && pom != nil {
		lic := detectLicense(pom)
		node.License  = lic
		node.Copyleft = isCopyleft(lic)
		for _, d := range pom.Dependencies {
			if skipScope(d.Scope, d.Optional) {
				continue
			}
			cga := d.GroupID + "/" + d.ArtifactID
			cv := d.Version
			if cv == "" {
				cv = "unknown"
			}
			child := buildFullBFS(d.GroupID, d.ArtifactID, cv, node.Name+"@"+eff, top, visited)
			if child != nil {
				node.Children = append(node.Children, child)
			}
		}
	}
	return node
}

// BFS expansions -> final flatten
func flattenBFS(n *BFSNode, lang string, out *[]FlatDep) {
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
		TopLevel: n.Name, // Or we can store a separate "TopLevel" if desired
		Copyleft: n.Copyleft,
		Language: lang,
		RepoInfo: link,
	}
	*out = append(*out, fd)
	for _, c := range n.Children {
		flattenBFS(c, lang, out)
	}
}

// ----------------------------------------------------------------------
// 9) FLATDEP + BFSSECTION
// ----------------------------------------------------------------------

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

// BFS for direct => doBFSForDirect
func doBFSForDirect(depMap map[string]string, filePath, lang string) BFSSection {
	visited := make(map[string]bool)
	var roots []*BFSNode
	var flat []FlatDep

	// Build BFS roots from direct
	for ga, ver := range depMap {
		g, a := splitGA(ga)
		node := buildFullBFS(g, a, ver, "direct", ga, visited)
		if node != nil {
			roots = append(roots, node)
		}
	}
	// flatten
	for _, r := range roots {
		flattenBFS(r, lang, &flat)
	}
	// sort so copyleft first, unknown second, others last
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
// 10) SCAN & PARSE: pom.xml, .toml, build.gradle
// ----------------------------------------------------------------------

// pom.xml
func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr != nil {
			return werr
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return nil
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

// .toml
func findTOMLFile(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr != nil {
			return werr
		}
		if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}

func parseTomlFile(filePath string) (map[string]string, error) {
	dat, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, err
	}
	res := make(map[string]string)
	libraries := dat.Get("libraries")
	if libraries == nil {
		return nil, nil // no "libraries" => no direct deps
	}
	libTree, ok := libraries.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not a valid table in %s", filePath)
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
		parts := strings.Split(mod, ":")
		if len(parts) < 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		key := g + "/" + a
		res[key] = verRef
	}
	return res, nil
}

// build.gradle
func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr != nil {
			return werr
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}

func parseBuildGradleFile(filePath string) (map[string]string, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(dat)
	var res = make(map[string]string)

	// We can also parse variables
	varRe := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	varMatches := varRe.FindAllStringSubmatch(content, -1)
	varMap := make(map[string]string)
	for _, mm := range varMatches {
		varMap[mm[1]] = mm[2]
	}

	depRe := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := depRe.FindAllStringSubmatch(content, -1)
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
			// Expand if it references a variable
			if strings.Contains(v, "${") {
				re2 := regexp.MustCompile(`\$\{([^}]+)\}`)
				v = re2.ReplaceAllStringFunc(v, func(s string) string {
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
		key := fmt.Sprintf("%s/%s", g, a)
		res[key] = v
	}
	return res, nil
}

// ----------------------------------------------------------------------
// 11) MAIN HTML REPORT + BFS
// ----------------------------------------------------------------------

type BFSSection struct {
	FilePath  string
	BFSNodes  []*BFSNode
	Flattened []FlatDep
}

type finalData struct {
	Summary        string
	PomSections    []BFSSection
	TomlSections   []BFSSection
	GradleSections []BFSSection
}

// Our final HTML template
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

// 12) MAIN
func main() {
	// Start BFS concurrency worker pool
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		depMap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("Error parse POM => %s: %v\n", pf, err)
			continue
		}
		bfsSec := doBFSForDirect(depMap, pf, "maven")
		pomSections = append(pomSections, bfsSec)
		totalPom += len(bfsSec.Flattened)
	}

	// 2) TOML
	tomlFiles, _ := findTOMLFile(".")
	var tomlSections []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		depMap, err := parseTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML => %s: %v\n", tf, err)
			continue
		}
		if depMap == nil {
			continue
		}
		bfsSec := doBFSForDirect(depMap, tf, "toml")
		tomlSections = append(tomlSections, bfsSec)
		totalToml += len(bfsSec.Flattened)
	}

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		depMap, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle => %s: %v\n", gf, err)
			continue
		}
		bfsSec := doBFSForDirect(depMap, gf, "gradle")
		gradleSections = append(gradleSections, bfsSec)
		totalGradle += len(bfsSec.Flattened)
	}

	// Shut down BFS concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Count copyleft
	copyleftCount := 0
	for _, sec := range pomSections {
		for _, fd := range sec.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range tomlSections {
		for _, fd := range sec.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}
	for _, sec := range gradleSections {
		for _, fd := range sec.Flattened {
			if isCopyleft(fd.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM total: %d, TOML total: %d, Gradle total: %d, Copyleft: %d",
		totalPom, totalToml, totalGradle, copyleftCount)

	data := struct {
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
		"isCopyleft": func(license string) bool {
			return isCopyleft(license)
		},
		"buildBFSHTML": func(n *BFSNode) template.HTML {
			return template.HTML(buildBFSHTML(n))
		},
	}
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error =>", err)
		return
	}
	out, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Println("Create file error =>", err)
		return
	}
	defer out.Close()

	if e2 := tmpl.Execute(out, data); e2 != nil {
		fmt.Println("Template exec error =>", e2)
		return
	}

	fmt.Println("license-full-bfs-report.html generated successfully!")
}

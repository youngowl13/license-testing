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
// Global Config & Worker Pool
// ----------------------------------------------------------------------

const (
	workerCount  = 5
	fetchTimeout = 30 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map   // key: "group:artifact:version" → *MavenPOM
	bfsCache     sync.Map   // key: "group/artifact@version" → *BFSNode
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// Types for Fetching
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
// License Detection (Comprehensive Copyleft)
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
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) || strings.EqualFold(license, spdxID)) {
			return true
		}
	}
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
// Maven POM Fetching
// ----------------------------------------------------------------------

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

type MavenPOM struct {
	GroupID      string
	ArtifactID   string
	Version      string
	Licenses     []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
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

func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	if p, err := fetchPOMFromURL(urlC); err == nil && p != nil {
		return p, nil
	}
	if p, err := fetchPOMFromURL(urlG); err == nil && p != nil {
		return p, nil
	}
	return nil, fmt.Errorf("cannot fetch remote POM for %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if err := dec.Decode(&pom); err != nil {
		return nil, err
	}
	return &pom, nil
}

// ----------------------------------------------------------------------
// Fallback Version Functions
// ----------------------------------------------------------------------

func fallbackVersionIfUnknown(g, a, orig string) (string, error) {
	if strings.ToLower(orig) != "unknown" {
		return orig, nil
	}
	latest, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return latest, nil
}

func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, err := fetchLatestVersionFromURL(urlC); err == nil && v != "" {
		return v, nil
	}
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, err := fetchLatestVersionFromURL(urlG); err == nil && v != "" {
		return v, nil
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
		return "", fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
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
	if err := xml.Unmarshal(data, &md); err != nil {
		return "", err
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
// Utility Functions: splitGA, buildRepoLink
// ----------------------------------------------------------------------

func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

func buildRepoLink(g, a, v string) string {
	if g == "" || a == "" {
		q := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, v)
}

// ----------------------------------------------------------------------
// BFS Node Type and Full BFS with Caching
// ----------------------------------------------------------------------

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
	if visited[key] {
		return nil
	}
	visited[key] = true

	if cached, ok := bfsCache.Load(key); ok {
		orig := cached.(*BFSNode)
		clone := cloneBFSNode(orig)
		clone.Parent = parent
		clone.TopLevel = top
		return clone
	}

	eff, err := fallbackVersionIfUnknown(g, a, v)
	if err != nil {
		eff = v
	}
	node := &BFSNode{
		Name:     g + "/" + a,
		Version:  eff,
		Parent:   parent,
		TopLevel: top,
		License:  "Unknown",
	}
	pom, err := concurrentFetchPOM(g, a, eff)
	if err == nil && pom != nil {
		lic := detectLicense(pom)
		node.License = lic
		node.Copyleft = isCopyleft(lic)
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
	bfsCache.Store(key, node)
	return node
}

func cloneBFSNode(orig *BFSNode) *BFSNode {
	clone := &BFSNode{
		Name:     orig.Name,
		Version:  orig.Version,
		License:  orig.License,
		Copyleft: orig.Copyleft,
	}
	for _, c := range orig.Children {
		clone.Children = append(clone.Children, cloneBFSNode(c))
	}
	return clone
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

// ----------------------------------------------------------------------
// 7) FINAL FLAT DEP STRUCTURE & BFSSection (declare once)
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

// ----------------------------------------------------------------------
// 8) FINAL DATA STRUCTURE FOR REPORT (declare once)
// ----------------------------------------------------------------------

type finalData struct {
	Summary        string
	PomSections    []BFSSection
	TomlSections   []BFSSection
	GradleSections []BFSSection
}

// ----------------------------------------------------------------------
// 9) TEMPLATE HELPER: buildBFSHTMLFunc
// ----------------------------------------------------------------------

func buildBFSHTMLFunc(n *BFSNode) template.HTML {
	return template.HTML(buildBFSHTML(n))
}

// ----------------------------------------------------------------------
// 10) FINAL HTML TEMPLATE
// ----------------------------------------------------------------------

var finalTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Full BFS License Report With Caching</title>
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
<h1>Full BFS License Report With Caching</h1>
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
    <p>No dependencies found.</p>
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
    <p>No dependencies found.</p>
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

// ----------------------------------------------------------------------
// 17) FINAL DATA STRUCTURE FOR REPORT IS finalData (declared above)
// ----------------------------------------------------------------------

// ----------------------------------------------------------------------
// 18) MAIN FUNCTION
// ----------------------------------------------------------------------

func main() {
	// Start worker pool
	for i := 0; i < workerCount; i++ {
		wgWorkers.Add(1)
		go pomWorker()
	}

	// Process POM files
	pomFiles, _ := findAllPOMFiles(".")
	var pomSecs []BFSSection
	var totalPom int
	for _, pf := range pomFiles {
		dmap, err := parseOnePomFile(pf)
		if err != nil {
			fmt.Printf("Error parsing POM file %s: %v\n", pf, err)
			continue
		}
		sec := doBFSForDirect(dmap, pf, "maven")
		pomSecs = append(pomSecs, sec)
		totalPom += len(sec.Flattened)
	}

	// Process TOML files
	tomlFiles, _ := findTOMLFile(".")
	var tomlSecs []BFSSection
	var totalToml int
	for _, tf := range tomlFiles {
		dmap, err := parseOneTomlFile(tf)
		if err != nil {
			fmt.Printf("Error parsing TOML file %s: %v\n", tf, err)
			continue
		}
		if dmap == nil {
			continue
		}
		sec := doBFSForDirect(dmap, tf, "toml")
		tomlSecs = append(tomlSecs, sec)
		totalToml += len(sec.Flattened)
	}

	// Process Gradle files
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSecs []BFSSection
	var totalGradle int
	for _, gf := range gradleFiles {
		dmap, err := parseOneGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parsing Gradle file %s: %v\n", gf, err)
			continue
		}
		sec := doBFSForDirect(dmap, gf, "gradle")
		gradleSecs = append(gradleSecs, sec)
		totalGradle += len(sec.Flattened)
	}

	// Shut down worker pool
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Count copyleft items
	copyleftCount := 0
	for _, s := range pomSecs {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range tomlSecs {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}
	for _, s := range gradleSecs {
		for _, d := range s.Flattened {
			if isCopyleft(d.License) {
				copyleftCount++
			}
		}
	}

	summary := fmt.Sprintf("POM: %d, TOML: %d, Gradle: %d, Copyleft: %d", totalPom, totalToml, totalGradle, copyleftCount)
	finalOut := finalData{
		Summary:        summary,
		PomSections:    pomSecs,
		TomlSections:   tomlSecs,
		GradleSections: gradleSecs,
	}

	funcMap := template.FuncMap{
		"isCopyleft":   isCopyleft,
		"buildBFSHTML": buildBFSHTMLFunc,
	}
	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalTemplate)
	if err != nil {
		fmt.Println("Template parse error:", err)
		return
	}
	f, err := os.Create("license-full-bfs-report.html")
	if err != nil {
		fmt.Println("Error creating report file:", err)
		return
	}
	defer f.Close()
	if err := tmpl.Execute(f, finalOut); err != nil {
		fmt.Println("Template execution error:", err)
		return
	}
	fmt.Println("license-full-bfs-report.html generated successfully!")
}

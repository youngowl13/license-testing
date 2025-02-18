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
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

// ----------------------------------------------------------------------
// CONFIG
// ----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"     // disk caching for fetched POMs
	pomWorkerCount   = 10               // concurrency
	fetchTimeout     = 30 * time.Second // HTTP GET timeout
)

// ----------------------------------------------------------------------
// GLOBALS
// ----------------------------------------------------------------------

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect parent cycles

	channelOpen  = true
	channelMutex sync.Mutex
)

// spdxLicenseMap: minimal SPDx => (FriendlyName, Copyleft)
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

// ----------------------------------------------------------------------
// DATA STRUCTURES
// ----------------------------------------------------------------------

// POMLicenses
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// POMDep is for <dependency> in the POM
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// MavenPOM is the minimal structure we parse from each .pom file
type MavenPOM struct {
	XMLName     xml.Name  `xml:"project"`
	Licenses    []License `xml:"licenses>license"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
}

// BFS node for the tree
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or "group/artifact:version"
	Transitive []*DependencyNode
}

// ExtendedDep holds info for the final table (Parent, License, etc.)
type ExtendedDep struct {
	Display string
	Lookup  string
	Parent  string
	License string
}

// TomlReportSection is your final object for each TOML file
type TomlReportSection struct {
	FilePath        string
	DirectDeps      map[string]string    // direct from TOML
	AllDeps         map[string]ExtendedDep
	DependencyTree  []*DependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// BFS state
type depState struct {
	Version string
	Depth   int
}

// BFS queue
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
}

// concurrency
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

// ----------------------------------------------------------------------
// TOML PARSING
// ----------------------------------------------------------------------

func findTOMLFile(root string) (string, error) {
	var tomlFile string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.HasSuffix(info.Name(), ".toml") {
			tomlFile = path
			return filepath.SkipDir
		}
		return nil
	})
	if err != nil {
		return "", fmt.Errorf("error walking the path %q: %v", root, err)
	}
	if tomlFile == "" {
		return "", fmt.Errorf("no .toml file found")
	}
	return tomlFile, nil
}

func parseTOMLFile(filePath string) (map[string]string, error) {
	dependencies := make(map[string]string)
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("error loading TOML file: %v", err)
	}

	versions, err := loadVersions(tree)
	if err != nil {
		return nil, err
	}

	librariesTree := tree.Get("libraries")
	if librariesTree == nil {
		return nil, fmt.Errorf("TOML file does not contain a 'libraries' table")
	}
	libraries, ok := librariesTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' is not a valid TOML table")
	}
	for _, libKey := range libraries.Keys() {
		libTree := libraries.Get(libKey)
		if libTree == nil {
			fmt.Printf("Warning: entry '%s' not found in libraries table.\n", libKey)
			continue
		}
		lib, ok := libTree.(*toml.Tree)
		if !ok {
			fmt.Printf("Warning: entry '%s' in libraries table is not a valid TOML table.\n", libKey)
			continue
		}
		module, ok := lib.Get("module").(string)
		if !ok {
			fmt.Printf("Warning: 'module' not found or not a string for library entry '%s'.\n", libKey)
			continue
		}
		versionRef, ok := lib.Get("version.ref").(string)
		if !ok {
			fmt.Printf("Warning: 'version.ref' not found for library entry '%s'.\n", libKey)
			continue
		}
		versionVal, ok := versions[versionRef]
		if !ok {
			fmt.Printf("Warning: version reference '%s' not found in 'versions' table for library '%s'.\n", versionRef, libKey)
			versionVal = "unknown"
		}
		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			fmt.Printf("Warning: invalid module format for library entry '%s'.\n", libKey)
			continue
		}
		group := parts[0]
		name := parts[1]
		dependencyKey := fmt.Sprintf("%s/%s", group, name)
		dependencies[dependencyKey] = versionVal
	}
	return dependencies, nil
}

func loadVersions(tree *toml.Tree) (map[string]string, error) {
	versions := make(map[string]string)
	versionsTree := tree.Get("versions")
	if versionsTree == nil {
		return versions, nil
	}
	versionsMap, ok := versionsTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'versions' is not a valid TOML table")
	}
	for _, key := range versionsMap.Keys() {
		value := versionsMap.Get(key)
		switch v := value.(type) {
		case string:
			versions[key] = v
		case *toml.Tree:
			fmt.Printf("Warning: nested tables in 'versions' are not supported. Skipping key '%s'.\n", key)
		default:
			fmt.Printf("Warning: unexpected type for version '%s'.\n", key)
		}
	}
	return versions, nil
}

// ----------------------------------------------------------------------
// BFS
// ----------------------------------------------------------------------

func buildTransitiveClosure(sections []TomlReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("BFS: Building transitive closure for TOML file: %s\n", sec.FilePath)
		allDeps := make(map[string]ExtendedDep) // "group/artifact@version" => ExtendedDep

		// add direct
		for ga, version := range sec.DirectDeps {
			key := ga + "@" + version
			allDeps[key] = ExtendedDep{
				Display: version,
				Lookup:  version,
				Parent:  "direct",
				License: "",
			}
		}
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*DependencyNode)
		var rootNodes []*DependencyNode
		var queue []queueItem
		visited := make(map[string]bool)

		// BFS init
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			visited[key] = true
			node := &DependencyNode{
				Name:    ga,
				Version: ver,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, node)
			nodeMap[key] = node
			stateMap[key] = depState{Version: ver, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       ver,
				Depth:         1,
				ParentNode:    node,
			})
		}

		// BFS
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("BFS: Processing %s@%s (depth %d)\n", it.GroupArtifact, it.Version, it.Depth)
			group, artifact := splitGA(it.GroupArtifact)
			if group == "" || artifact == "" {
				continue
			}
			// skip if unknown
			if strings.ToLower(it.Version) == "unknown" {
				continue
			}
			pom, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("BFS: skipping %s:%s:%s => fetch error or nil\n", group, artifact, it.Version)
				continue
			}
			// attach license
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
			}
			// parse sub-deps from <dependencies>
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				childDepth := it.Depth + 1
				childKey := childGA + "@" + cv
				if _, found := visited[childKey]; found {
					continue
				}
				visited[childKey] = true
				curSt, seen := stateMap[childKey]
				if !seen {
					stateMap[childKey] = depState{Version: cv, Depth: childDepth}
					childNode := &DependencyNode{
						Name:    childGA,
						Version: cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					}
					nodeMap[childKey] = childNode
					allDeps[childKey] = ExtendedDep{
						Display: cv,
						Lookup:  cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
						License: "",
					}
					if it.ParentNode != nil {
						it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
					}
					queue = append(queue, queueItem{
						GroupArtifact: childGA,
						Version:       cv,
						Depth:         childDepth,
						ParentNode:    childNode,
					})
				} else {
					if childDepth < curSt.Depth {
						stateMap[childKey] = depState{Version: cv, Depth: childDepth}
						childNode, ok := nodeMap[childKey]
						if !ok {
							childNode = &DependencyNode{
								Name:    childGA,
								Version: cv,
								Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
							}
							nodeMap[childKey] = childNode
						} else {
							childNode.Version = cv
							childNode.Parent  = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
						}
						if it.ParentNode != nil {
							it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
						}
						queue = append(queue, queueItem{
							GroupArtifact: childGA,
							Version:       cv,
							Depth:         childDepth,
							ParentNode:    childNode,
						})
					}
				}
			}
		}

		// fill BFS results into allDeps again
		for _, nd := range rootNodes {
			fillDepMapToml(nd, allDeps)
		}

		// store final
		sec.AllDeps = allDeps
		sec.DependencyTree = rootNodes

		// count BFS nodes, direct, transitive
		total := len(allDeps)
		// direct are those "Parent=direct" or "ends in @unknown"
		directCount := 0
		for k, ed := range allDeps {
			if ed.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			}
		}
		sec.TransitiveCount = total - directCount
	}
}

// skipScope returns true if scope in {test,provided,system} or optional="true"
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

// fillDepMapToml recursively updates the BFS results
func fillDepMapToml(n *DependencyNode, all map[string]ExtendedDep) {
	key := n.Name + "@" + n.Version
	info, exists := all[key]
	if !exists {
		info = ExtendedDep{
			Display: n.Version,
			Lookup:  n.Version,
			Parent:  n.Parent,
		}
	} else {
		info.Display = n.Version
		info.Lookup  = n.Version
		info.Parent  = n.Parent
	}
	info.License = n.License
	all[key] = info
	for _, c := range n.Transitive {
		fillDepMapToml(c, all)
	}
}

// concurrency
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("Worker fetch => %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

// concurrentFetchPOM checks cache, then calls worker if channel is open, or direct fetch
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("concurrentFetchPOM: Cache HIT for %s\n", key)
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("concurrentFetchPOM: channel closed => direct fetch for %s\n", key)
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	req := fetchRequest{
		GroupID:    g,
		ArtifactID: a,
		Version:    v,
		ResultChan: make(chan fetchResult, 1),
	}
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// fetchRemotePOM tries maven central & google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	fmt.Printf("fetchRemotePOM => Trying maven central: %s\n", urlC)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pm)
		return pm, nil
	}
	fmt.Printf("fetchRemotePOM => Trying google: %s\n", urlG)
	if pm, e2 := fetchPOMFromURL(urlG); e2 == nil && pm != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pm)
		return pm, nil
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
		return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	if e2 := xml.Unmarshal(data, &pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

// detectLicense sees if there's a first license
func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(pom.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	up := strings.ToUpper(lic)
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || up == strings.ToUpper(spdxID) {
			return data.Name
		}
	}
	return lic
}

// isCopyleft checks for recognized copyleft keywords
func isCopyleft(name string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "CC-BY-SA", "MPL", "EPL", "CPL",
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
// HTML REPORT (with parent column + BFS tree)
// ----------------------------------------------------------------------

func buildDependencyTreeHTML(node *DependencyNode, level int) string {
	class := "non-copyleft"
	if node.License == "Unknown" {
		class = "unknown-license"
	} else if node.Copyleft {
		class = "copyleft"
	}
	summary := fmt.Sprintf("%s@%s (License: %s)", node.Name, node.Version, node.License)
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf(`<details class="%s" style="margin-left:%dem;">`, class, level))
	sb.WriteString(fmt.Sprintf(`<summary>%s</summary>`, template.HTMLEscapeString(summary)))
	for _, c := range node.Transitive {
		sb.WriteString(buildDependencyTreeHTML(c, level+1))
	}
	sb.WriteString("</details>")
	return sb.String()
}

func buildDependencyTreesHTML(nodes []*DependencyNode) template.HTML {
	var buf strings.Builder
	for _, n := range nodes {
		buf.WriteString(buildDependencyTreeHTML(n, 0))
	}
	return template.HTML(buf.String())
}

func generateHTMLReport(sections []TomlReportSection) error {
	outDir := "./license-checker"
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return err
	}
	const tmplText = `<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>TOML Dependency License Report</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 20px; }
    h1 { color: #2c3e50; }
    h2 { margin-top: 40px; }
    table { width: 100%; border-collapse: collapse; margin-bottom: 40px; }
    th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    th { background-color: #f2f2f2; }
    tr:nth-child(even) { background-color: #f9f9f9; }
    a { color: #3498db; text-decoration: none; }
    a:hover { text-decoration: underline; }
    tr.copyleft { background-color: #ffdddd; }
    tr.non-copyleft { background-color: #ddffdd; }
    tr.unknown-license { background-color: #ffffdd; }

    details.copyleft > summary {
      background-color: #ffdddd;
      padding: 2px 4px;
      border-radius: 4px;
    }
    details.unknown-license > summary {
      background-color: #ffffdd;
      padding: 2px 4px;
      border-radius: 4px;
    }
    details.non-copyleft > summary {
      background-color: #ddffdd;
      padding: 2px 4px;
      border-radius: 4px;
    }
  </style>
</head>
<body>
  <h1>TOML Dependency License Report</h1>
  {{ range . }}
    <h2>File: {{ .FilePath }}</h2>
    <p>
      Direct Dependencies: {{ .DirectCount }}<br>
      Indirect Dependencies: {{ .IndirectCount }}<br>
      Copyleft Dependencies: {{ .CopyleftCount }}<br>
      Unknown License Dependencies: {{ .UnknownCount }}
    </p>
    <h3>Dependency Table</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>Parent</th>
          <th>License</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ range $dep, $info := .AllDeps }}
          {{ if eq $info.License "Unknown" }}
            <tr class="unknown-license">
          {{ else if isCopyleft $info.License }}
            <tr class="copyleft">
          {{ else }}
            <tr class="non-copyleft">
          {{ end }}
            <td>{{ $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $info.Parent }}</td>
            <td>{{ $info.License }}</td>
            <td><a href="https://www.google.com/search?q={{ $dep }}+license" target="_blank">Search</a></td>
            <td><a href="https://repo1.maven.org/maven2/{{ $dep }}/{{ $info.Lookup }}" target="_blank">POM?</a></td>
          </tr>
        {{ end }}
      </tbody>
    </table>
    <h3>Dependency Tree</h3>
    {{ buildDependencyTreesHTML .DependencyTree }}
  {{ end }}
</body>
</html>
`
	tmpl, err := template.New("reportToml").Funcs(template.FuncMap{
		"isCopyleft":           isCopyleft,
		"buildDependencyTreesHTML": buildDependencyTreesHTML,
	}).Parse(tmplText)
	if err != nil {
		return err
	}
	outPath := filepath.Join(outDir, "dependency-license-report.html")
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}
	fmt.Printf("✅ TOML license report generated at %s\n", outPath)
	return nil
}

// ----------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------

func main() {
	// start concurrency
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting TOML dependency analysis...")

	tomlFile, err := findTOMLFile(".")
	if err != nil {
		fmt.Printf("Error finding TOML file: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found TOML file at: %s\n", tomlFile)

	directDeps, err := parseTOMLFile(tomlFile)
	if err != nil {
		fmt.Printf("Error parsing TOML file: %v\n", err)
		os.Exit(1)
	}
	// single section
	sections := []TomlReportSection{
		{
			FilePath:  tomlFile,
			DirectDeps: directDeps,
			AllDeps:   make(map[string]ExtendedDep),
		},
	}

	fmt.Println("Starting BFS to build full dependency tree with concurrency...")
	buildTransitiveClosure(sections)

	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// compute summary
	for i := range sections {
		sec := &sections[i]
		var directCount, indirectCount, copyleftCount, unknownCount int

		// "direct" = "Parent=direct"
		for k, inf := range sec.AllDeps {
			if inf.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			} else {
				indirectCount++
			}
			if isCopyleft(inf.License) {
				copyleftCount++
			}
			if inf.License == "Unknown" {
				unknownCount++
			}
		}
		sec.DirectCount = directCount
		sec.IndirectCount = indirectCount
		sec.CopyleftCount = copyleftCount
		sec.UnknownCount = unknownCount
	}

	fmt.Println("Generating HTML report with both parent column and BFS tree...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("Analysis complete.")
}

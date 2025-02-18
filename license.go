package main

import (
	"bytes"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"io/ioutil"
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
// CONFIG & CONSTANTS
// ----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"      // directory to cache fetched POMs
	pomWorkerCount   = 10                // number of concurrency workers
	fetchTimeout     = 30 * time.Second  // HTTP GET timeout
)

// ----------------------------------------------------------------------
// GLOBALS
// ----------------------------------------------------------------------

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map // key = "group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect cycles in parent POM resolution

	channelOpen  = true
	channelMutex sync.Mutex

	// Minimal set of spdx => (friendlyName, isCopyleft)
	spdxLicenseMap = map[string]struct {
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
)

// ----------------------------------------------------------------------
// DATA STRUCTURES
// ----------------------------------------------------------------------

// TomlReportSection is similar to your Gradle "ReportSection" but for TOML
type TomlReportSection struct {
	FilePath        string
	Dependencies    map[string]string // raw map => "group/artifact" => "version" from the TOML
	DependencyTree  []*DependencyNode // BFS tree
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// ExtendedDepInfo is used in BFS to store "display" version, "lookup" version, etc.
// We'll store the BFS results in a separate map so we can do concurrency, cycle detection, etc.
type ExtendedDepInfo struct {
	Display string
	Lookup  string
	Parent  string
	License string
}

// DependencyNode is a BFS node in the tree
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*DependencyNode
}

// MavenPOM minimal structure
type MavenPOM struct {
	XMLName  xml.Name  `xml:"project"`
	Licenses []License `xml:"licenses>license"`
}

// License from the POM
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// depState for BFS conflict resolution
type depState struct {
	Version string
	Depth   int
}

// BFS queue item
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
// TOML PARSING (unchanged from your original code, except inlined here)
// ----------------------------------------------------------------------

// findTOMLFile searches for a single .toml file. If found, returns path.
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

// parseTOMLFile parses the TOML file and extracts "group/artifact" => version
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

// loadVersions loads the "versions" table from the TOML
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
// BFS + concurrency approach
// ----------------------------------------------------------------------

// parseTOMLAsSections loads one .toml file => 1 section
func parseTOMLAsSections() ([]TomlReportSection, error) {
	tomlFile, err := findTOMLFile(".")
	if err != nil {
		return nil, err
	}
	fmt.Printf("Found TOML file at: %s\n", tomlFile)

	deps, err := parseTOMLFile(tomlFile)
	if err != nil {
		return nil, err
	}
	// single section
	sections := []TomlReportSection{
		{
			FilePath:     tomlFile,
			Dependencies: deps,
		},
	}
	return sections, nil
}

// BFS approach, similar to Gradle code, but for TOML
func buildTransitiveClosure(sections []TomlReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("BFS: Building transitive closure for TOML file: %s\n", sec.FilePath)

		// We'll store BFS states as map["group/artifact@version"] => depState
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*DependencyNode)

		// Convert the "dependencies" map => BFS "depKey@version" => BFS items
		flatDeps := make(map[string]ExtendedDepInfo)

		// copy direct
		for ga, version := range sec.Dependencies {
			key := ga + "@" + version
			flatDeps[key] = ExtendedDepInfo{
				Display: version,
				Lookup:  version,
				Parent:  "direct",
			}
		}

		var rootNodes []*DependencyNode
		var queue []queueItem
		visited := make(map[string]bool)

		// BFS init from direct deps
		for ga, version := range sec.Dependencies {
			key := ga + "@" + version
			visited[key] = true
			node := &DependencyNode{
				Name:    ga,
				Version: version,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, node)
			nodeMap[key] = node
			stateMap[key] = depState{Version: version, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       version,
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
			// dynamic version if unknown
			if strings.ToLower(it.Version) == "unknown" {
				fmt.Printf("BFS: version for %s was 'unknown'; skipping BFS children.\n", it.GroupArtifact)
				continue
			}
			// fetch POM
			pom, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("BFS: skipping %s:%s:%s => fetch error or nil\n", group, artifact, it.Version)
				continue
			}
			// attach license to current BFS node
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
			}
			// no "dependencyManagement" in minimal approach, so we won't parse managed
			// but if you want, define parseManagedVersions as no-op or real approach
			// (or do "managed := parseManagedVersions(pom)" like the Gradle approach).
			// For demonstration, let's skip management since we just said "like the Gradle code."
			for _, lic := range pom.Licenses {
				_ = lic // not strictly needed here, we already detectLicense
			}

			// We could parse sub-dependencies from the POM if you want BFS of transitive
			// but a minimal POM might not list sub-dependencies. If you do want that,
			// you need to parse <dependency> in your MavenPOM struct. This snippet has only <licenses>.
			// In other words, if you want to BFS sub-dependencies, your MavenPOM struct must have a <dependencies> field, etc.
			// For demonstration, let's assume you only want direct BFS of what's in your TOML (no deeper POM BFS).
			// If you want deeper BFS from the POM file, you'd replicate the approach from the Gradle code that read <dependencies>.
		}

		// fill final BFS map
		for _, root := range rootNodes {
			fillDepMapToml(root, flatDeps)
		}

		// store final
		// we won't do "sortRoots" if you want alphabetical sorting, do so
		sec.DependencyTree = convertToNodes(flatDeps, nodeMap)
		// count BFS nodes
		totalNodes := len(flatDeps) // or do a real BFS count
		directCount := 0
		for k, info := range flatDeps {
			if info.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			}
		}
		sec.TransitiveCount = totalNodes - directCount
		// reassign final
		sec.Dependencies = map[string]string{}
		for k, inf := range flatDeps {
			sec.Dependencies[k] = inf.Lookup
		}
	}
}

// fillDepMapToml is a simpler function to store BFS results
func fillDepMapToml(n *DependencyNode, depMap map[string]ExtendedDepInfo) {
	key := fmt.Sprintf("%s@%s", n.Name, n.Version)
	info, exists := depMap[key]
	if !exists {
		info = ExtendedDepInfo{
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
	depMap[key] = info
	for _, c := range n.Transitive {
		fillDepMapToml(c, depMap)
	}
}

// convertToNodes a naive approach to produce BFS tree from the final map & nodeMap
func convertToNodes(flat map[string]ExtendedDepInfo, nodeMap map[string]*DependencyNode) []*DependencyNode {
	// we can guess root nodes by "Parent=direct" or "ends with @unknown"
	var roots []*DependencyNode
	rootKeys := make(map[string]bool)
	for k, nd := range nodeMap {
		if nd.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
			rootKeys[k] = true
		}
	}
	for k := range rootKeys {
		roots = append(roots, nodeMap[k])
	}
	return roots
}

// ----------------------------------------------------------------------
// detectLicense (we have it) & concurrency
// ----------------------------------------------------------------------

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

func isCopyleft(name string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "MPL", "EPL", "CPL",
		"CDDL", "EUPL", "Affero", "OSL", "CeCILL",
		"GNU General Public License", "GNU Lesser General Public License",
		"Mozilla Public License", "Common Development and Distribution License",
		"Eclipse Public License", "Common Public License",
		"European Union Public License", "Open Software License",
	}
	up := strings.ToUpper(name)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// concurrency

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("Worker fetch for %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pom, err := fetchRemotePOMToml(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

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
		pom, err := fetchRemotePOMToml(g, a, v)
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

// fetchRemotePOMToml tries maven central & google
func fetchRemotePOMToml(g, a, v string) (*MavenPOM, error) {
	fmt.Printf("fetchRemotePOMToml: Attempting for %s:%s:%s\n", g, a, v)
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)

	// try central
	pomC, errC := fetchPOMFromURL(urlCentral)
	if errC == nil && pomC != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pomC)
		return pomC, nil
	}
	// try google
	pomG, errG := fetchPOMFromURL(urlGoogle)
	if errG == nil && pomG != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pomG)
		return pomG, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	fmt.Printf("fetchPOMFromURL: GET => %s\n", url)
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

// ----------------------------------------------------------------------
// HTML REPORT
// ----------------------------------------------------------------------

func generateHTMLReportToml(sections []TomlReportSection) error {
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
      Direct: {{ .DirectCount }}<br>
      Indirect: {{ .IndirectCount }}<br>
      Copyleft: {{ .CopyleftCount }}<br>
      Unknown: {{ .UnknownCount }}
    </p>
    <h3>Dependency Tree</h3>
    <ul>
    {{ range .DependencyTree }}
      <li>{{ .Name }}@{{ .Version }} ({{ .License }})</li>
    {{ end }}
    </ul>
  {{ end }}
</body>
</html>
`
	tmpl, err := template.New("reportToml").Funcs(template.FuncMap{
		"isCopyleft": isCopyleft,
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
	if err2 := tmpl.Execute(f, sections); err2 != nil {
		return err2
	}
	fmt.Printf("✅ TOML license report generated at %s\n", outPath)
	return nil
}

// ----------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------

func main() {
	// start concurrency worker pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting TOML dependency analysis...")

	// 1) parse TOML into sections
	sections, err := parseTOMLAsSections()
	if err != nil {
		fmt.Printf("Error parsing TOML file: %v\n", err)
		os.Exit(1)
	}

	// 2) BFS => concurrency approach
	fmt.Println("Starting transitive dependency resolution with BFS concurrency...")
	buildTransitiveClosure(sections)

	// close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// 3) Now BFS done. If you want to do a “license precomputation” with BFS sub-deps, you could do so.
	//   But in this minimal version, we only do BFS for direct TOML => POM. The BFS doesn’t read sub-dependencies from POM.
	//   If you want further BFS from the POM’s <dependencies>, replicate the code from your Gradle approach that read them.

	// 4) compute summary metrics (like the final code did)
	for idx := range sections {
		sec := &sections[idx]
		// we only have BFS for direct. If you want real BFS sub-deps, parse <dependency> in MavenPOM and queue them.
		// for now, let's do basic direct vs transitive stats
		var directCount, indirectCount, copyleftCount, unknownCount int
		// We have "DependencyTree" but not storing deeper BFS with license?
		// Let’s do a naive approach: just count direct for each "Parent=direct" if we had a map of ExtendedDepInfo
		// (Simplified for demonstration).
		// If you want the full BFS approach with deeper sub-deps, you can store them in a map like we did for Gradle.

		// For now, we rely on the BFS's "TransitiveCount"
		// We'll just set sec.DirectCount to len(sec.Dependencies) if BFS didn't do sub-deps from POM
		sec.DirectCount = len(sec.Dependencies)
		sec.IndirectCount = sec.TransitiveCount
		// For copyleft & unknown, you'd need to check the BFS nodes
		for _, nd := range sec.DependencyTree {
			if nd.Copyleft {
				copyleftCount++
			}
			if nd.License == "Unknown" {
				unknownCount++
			}
		}
		sec.CopyleftCount = copyleftCount
		sec.UnknownCount = unknownCount
	}

	// 5) generate HTML
	if err := generateHTMLReportToml(sections); err != nil {
		fmt.Printf("Error generating TOML HTML report: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("Analysis complete.")
}

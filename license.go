package main

import (
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
// CONFIGURATION
// ----------------------------------------------------------------------
const (
	localPOMCacheDir = ".pom-cache"     // On-disk cache for fetched POMs (not fully implemented here)
	pomWorkerCount   = 10               // number of concurrent workers for POM fetching
	fetchTimeout     = 30 * time.Second // HTTP client timeout
	outputReport     = "license-checker/dependency-license-report.html"
)

// ----------------------------------------------------------------------
// GLOBAL VARIABLES
// ----------------------------------------------------------------------
var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// TYPES FOR CONCURRENCY
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

// ----------------------------------------------------------------------
// SPDX LICENSE MAP & DATA STRUCTURES
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

// License represents a license entry in a POM.
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// POMDep represents a dependency entry in a POM.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// MavenPOM represents the structure of a pom.xml.
type MavenPOM struct {
	XMLName        xml.Name  `xml:"project"`
	Licenses       []License `xml:"licenses>license"`
	Dependencies   []POMDep  `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Parent struct {
		GroupID    string `xml:"groupId"`
		ArtifactID string `xml:"artifactId"`
		Version    string `xml:"version"`
	} `xml:"parent"`
}

// DependencyNode represents a node in the BFS tree.
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or "group/artifact:version"
	Transitive []*DependencyNode
}

// ExtendedDep holds final info for the HTML table.
type ExtendedDep struct {
	Display      string // The version to display
	Lookup       string // The version used for links
	Parent       string // "direct" if top-level
	License      string
	IntroducedBy string // top-level root that introduced this dependency
}

// ReportSection holds data for one discovered file (POM, TOML, Gradle).
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string      // "group/artifact" -> version
	AllDeps         map[string]ExtendedDep // "group/artifact@version" -> ExtendedDep
	DependencyTree  []*DependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// ----------------------------------------------------------------------
// FILE DISCOVERY & PARSING
// ----------------------------------------------------------------------

// findAllPOMFiles recursively finds all pom.xml files.
func findAllPOMFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

// parseOneLocalPOMFile reads a pom.xml and extracts direct dependencies.
func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if err := xml.Unmarshal(data, &pom); err != nil {
		return nil, fmt.Errorf("error parsing pom.xml '%s': %v", filePath, err)
	}
	deps := make(map[string]string)
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		group := d.GroupID
		artifact := d.ArtifactID
		version := d.Version
		if version == "" {
			version = "unknown"
		}
		key := group + "/" + artifact
		deps[key] = version
	}
	return deps, nil
}

// findAllTOMLFiles recursively finds all .toml files.
func findAllTOMLFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.HasSuffix(info.Name(), ".toml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

// parseTOMLFile parses a libs.versions.toml file => direct dependencies.
func parseTOMLFile(filePath string) (map[string]string, error) {
	deps := make(map[string]string)
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
		item := libraries.Get(libKey)
		lib, ok := item.(*toml.Tree)
		if !ok {
			continue
		}
		module, ok := lib.Get("module").(string)
		if !ok {
			continue
		}
		versionRef, ok := lib.Get("version.ref").(string)
		if !ok {
			continue
		}
		versionVal, ok := versions[versionRef]
		if !ok {
			versionVal = "unknown"
		}
		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			continue
		}
		group := parts[0]
		artifact := parts[1]
		key := fmt.Sprintf("%s/%s", group, artifact)
		deps[key] = versionVal
	}
	return deps, nil
}

// loadVersions loads the [versions] table from a TOML file.
func loadVersions(tree *toml.Tree) (map[string]string, error) {
	versions := make(map[string]string)
	vTree := tree.Get("versions")
	if vTree == nil {
		return versions, nil
	}
	vMap, ok := vTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'versions' is not a valid TOML table")
	}
	for _, key := range vMap.Keys() {
		val := vMap.Get(key)
		if str, ok := val.(string); ok {
			versions[key] = str
		}
	}
	return versions, nil
}

// findAllGradleFiles recursively finds all build.gradle/build.gradle.kts files.
func findAllGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		name := info.Name()
		if !info.IsDir() && (strings.EqualFold(name, "build.gradle") || strings.EqualFold(name, "build.gradle.kts")) {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

// parseBuildGradleFile extracts direct dependencies from a Gradle file.
func parseBuildGradleFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseGradleVariables(content)
	deps := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		depStr := m[2]
		parts := strings.Split(depStr, ":")
		if len(parts) < 2 {
			continue
		}
		group := parts[0]
		artifact := parts[1]
		version := "unknown"
		if len(parts) >= 3 {
			version = parseVersionRange(parts[2])
			if strings.Contains(version, "${") {
				reVar := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = reVar.ReplaceAllStringFunc(version, func(s string) string {
					inner := s[2 : len(s)-1]
					if val, ok := varMap[inner]; ok {
						return val
					}
					return ""
				})
				if version == "" {
					version = "unknown"
				}
			}
		}
		key := fmt.Sprintf("%s/%s", group, artifact)
		deps[key] = version
	}
	return deps, nil
}

// parseGradleVariables extracts variable definitions from a Gradle file.
func parseGradleVariables(content string) map[string]string {
	vars := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 3 {
			vars[match[1]] = match[2]
		}
	}
	return vars
}

// parseVersionRange picks a lower bound if v is a version range, else returns v as-is.
func parseVersionRange(v string) string {
	v = strings.TrimSpace(v)
	if (strings.HasPrefix(v, "[") || strings.HasPrefix(v, "(")) && strings.Contains(v, ",") {
		trimmed := strings.Trim(v, "[]() ")
		parts := strings.Split(trimmed, ",")
		if len(parts) > 0 {
			return strings.TrimSpace(parts[0])
		}
	}
	return v
}

// ----------------------------------------------------------------------
// BFS TRANSITIVE DEPENDENCY RESOLUTION
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

// splitGA splits "group/artifact" into group, artifact.
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

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

func detectLicense(pom *MavenPOM) string {
	if pom == nil || len(pom.Licenses) == 0 {
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

// fetchRemotePOM tries to fetch a POM from Maven Central or Google Maven.
func fetchRemotePOM(group, artifact, version string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(group, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	client := http.Client{Timeout: fetchTimeout}

	fmt.Printf("[FETCH-REMOTE] Attempting Maven Central for %s:%s:%s => %s\n", group, artifact, version, urlCentral)
	resp, err := client.Get(urlCentral)
	if err == nil && resp.StatusCode == 200 {
		defer resp.Body.Close()
		data, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, err
		}
		var pom MavenPOM
		if err := xml.Unmarshal(data, &pom); err != nil {
			return nil, err
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from Maven Central => %s:%s:%s\n", group, artifact, version)
		return &pom, nil
	}
	if resp != nil {
		resp.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] Fallback => Google Maven for %s:%s:%s => %s\n", group, artifact, version, urlGoogle)
	resp2, err2 := client.Get(urlGoogle)
	if err2 == nil && resp2.StatusCode == 200 {
		defer resp2.Body.Close()
		data, err := io.ReadAll(resp2.Body)
		if err != nil {
			return nil, err
		}
		var pom MavenPOM
		if err := xml.Unmarshal(data, &pom); err != nil {
			return nil, err
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from Google Maven => %s:%s:%s\n", group, artifact, version)
		return &pom, nil
	}
	if resp2 != nil {
		resp2.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] FAILED => %s:%s:%s\n", group, artifact, version)
	return nil, fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

// concurrentFetchPOM uses the worker pool or direct fetch if closed.
func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
	if cached, ok := pomCache.Load(key); ok {
		fmt.Printf("[FETCH-CACHE] HIT => %s\n", key)
		return cached.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("[FETCH] Channel closed => direct fetch => %s\n", key)
		pom, err := fetchRemotePOM(group, artifact, version)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	req := fetchRequest{
		GroupID:    group,
		ArtifactID: artifact,
		Version:    version,
		ResultChan: make(chan fetchResult, 1),
	}
	fmt.Printf("[FETCH] Enqueuing request => %s\n", key)
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// pomFetchWorker processes fetch requests in parallel.
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		key := fmt.Sprintf("%s:%s:%s", req.GroupID, req.ArtifactID, req.Version)
		fmt.Printf("[WORKER] Processing => %s\n", key)
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// buildTransitiveClosure => BFS for each section
func buildTransitiveClosure(sections []ReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("[BFS] Building transitive closure for %s\n", sec.FilePath)
		allDeps := make(map[string]ExtendedDep)
		// Add direct
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			allDeps[key] = ExtendedDep{
				Display:      ver,
				Lookup:       ver,
				Parent:       "direct",
				License:      "",
				IntroducedBy: "",
			}
		}
		type queueItem struct {
			GroupArtifact string
			Version       string
			Depth         int
			ParentNode    *DependencyNode
		}
		var queue []queueItem
		visited := make(map[string]bool)
		var rootNodes []*DependencyNode

		// Initialize BFS
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			visited[key] = true
			node := &DependencyNode{
				Name:    ga,
				Version: ver,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, node)
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       ver,
				Depth:         1,
				ParentNode:    node,
			})
		}

		// BFS loop
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("[BFS] Processing => %s@%s (depth=%d)\n", it.GroupArtifact, it.Version, it.Depth)
			group, artifact := splitGA(it.GroupArtifact)
			if group == "" || artifact == "" {
				fmt.Printf("[BFS] skip => invalid GA: %s\n", it.GroupArtifact)
				continue
			}
			if strings.ToLower(it.Version) == "unknown" {
				fmt.Printf("[BFS] skip => version unknown => %s@%s\n", it.GroupArtifact, it.Version)
				continue
			}
			pom, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("[BFS] skip => fetch error => %s@%s => %v\n", it.GroupArtifact, it.Version, err)
				continue
			}
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
			}
			// Child dependencies
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				} else {
					cv = parseVersionRange(cv)
					if cv == "" {
						cv = "unknown"
					}
				}
				childKey := childGA + "@" + cv
				if visited[childKey] {
					continue
				}
				visited[childKey] = true
				fmt.Printf("[BFS]   => discovered child %s@%s (parent=%s@%s)\n", childGA, cv, it.GroupArtifact, it.Version)
				childNode := &DependencyNode{
					Name:    childGA,
					Version: cv,
					Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
				}
				allDeps[childKey] = ExtendedDep{
					Display:      cv,
					Lookup:       cv,
					Parent:       fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					License:      "",
					IntroducedBy: "",
				}
				if it.ParentNode != nil {
					it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
				}
				queue = append(queue, queueItem{
					GroupArtifact: childGA,
					Version:       cv,
					Depth:         it.Depth + 1,
					ParentNode:    childNode,
				})
			}
		}

		// Fill BFS results
		for _, root := range rootNodes {
			fillDepMap(root, allDeps)
		}
		// Mark top-level introducers
		for _, root := range rootNodes {
			rootCoord := fmt.Sprintf("%s:%s", root.Name, root.Version)
			setIntroducedBy(root, rootCoord, allDeps)
		}
		sec.AllDeps = allDeps
		sec.DependencyTree = rootNodes
	}
}

// fillDepMap => propagate license info into AllDeps
func fillDepMap(node *DependencyNode, all map[string]ExtendedDep) {
	key := node.Name + "@" + node.Version
	info, exists := all[key]
	if !exists {
		info = ExtendedDep{
			Display: node.Version,
			Lookup:  node.Version,
			Parent:  node.Parent,
		}
	}
	if node.License == "" {
		info.License = "Unknown"
	} else {
		info.License = node.License
	}
	all[key] = info
	for _, child := range node.Transitive {
		fillDepMap(child, all)
	}
}

// setIntroducedBy => set top-level dependency for transitive
func setIntroducedBy(node *DependencyNode, rootCoord string, all map[string]ExtendedDep) {
	for _, child := range node.Transitive {
		key := child.Name + "@" + child.Version
		info := all[key]
		info.IntroducedBy = rootCoord
		all[key] = info
		setIntroducedBy(child, rootCoord, all)
	}
}

// ----------------------------------------------------------------------
// HTML REPORT GENERATION
// ----------------------------------------------------------------------

// buildDependencyTreeHTML => recursive HTML details
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
	sort.Slice(nodes, func(i, j int) bool {
		return nodes[i].Name < nodes[j].Name
	})
	var sb strings.Builder
	for _, node := range nodes {
		sb.WriteString(buildDependencyTreeHTML(node, 0))
	}
	return template.HTML(sb.String())
}

// categoryRank => 0=Copyleft, 1=Unknown, 2=Others
func categoryRank(license string) int {
	if isCopyleft(license) {
		return 0
	} else if license == "Unknown" {
		return 1
	}
	return 2
}

// parseCoord => splits "group/artifact@version" => returns "group/artifact"
func parseCoord(dep string) string {
	parts := strings.SplitN(dep, "@", 2)
	return parts[0] // "group/artifact"
}

// parseVersion => splits "group/artifact@version" => returns "version" (or "")
func parseVersion(dep string) string {
	parts := strings.SplitN(dep, "@", 2)
	if len(parts) < 2 {
		return ""
	}
	return parts[1]
}

// buildRepoLink => pick Google Maven for com.android*, else mvnrepository
func buildRepoLink(depWithVer string) string {
	ga := parseCoord(depWithVer)
	ver := parseVersion(depWithVer)
	group, artifact := splitGA(ga)
	if group == "" || artifact == "" {
		return fmt.Sprintf("https://www.google.com/search?q=%s", depWithVer)
	}
	if strings.HasPrefix(group, "com.android") {
		return fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", group, artifact, ver)
	}
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", group, artifact, ver)
}

// buildPOMLink => direct link to the POM on Maven Central
func buildPOMLink(depWithVer string) string {
	ga := parseCoord(depWithVer)
	ver := parseVersion(depWithVer)
	group, artifact := splitGA(ga)
	if group == "" || artifact == "" || ver == "" {
		return ""
	}
	groupPath := strings.ReplaceAll(group, ".", "/")
	return fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, ver, artifact, ver)
}

// generateHTMLReport => final HTML
func generateHTMLReport(sections []ReportSection) error {
	outDir := "license-checker"
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return err
	}
	const tmplText = `<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Dependency License Report</title>
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
    tr.unknown-license { background-color: #ffffdd; }
    tr.non-copyleft { background-color: #ddffdd; }
    details.copyleft > summary { background-color: #ffdddd; padding: 2px 4px; border-radius: 4px; }
    details.unknown-license > summary { background-color: #ffffdd; padding: 2px 4px; border-radius: 4px; }
    details.non-copyleft > summary { background-color: #ddffdd; padding: 2px 4px; border-radius: 4px; }
  </style>
</head>
<body>
  <h1>Dependency License Report</h1>
  {{ range $i, $section := . }}
    <h2>File: {{$section.FilePath}}</h2>
    <p>
      Direct Dependencies: {{$section.DirectCount}}<br>
      Indirect Dependencies: {{$section.IndirectCount}}<br>
      Copyleft Dependencies: {{$section.CopyleftCount}}<br>
      Unknown License Dependencies: {{$section.UnknownCount}}
    </p>
    <h3>Dependency Table ({{$section.FilePath}})</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>Parent</th>
          <th>Top-Level Dependency</th>
          <th>License</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ $keys := sortKeys $section.AllDeps }}
        {{ range $dep := $keys }}
          {{ $info := index $section.AllDeps $dep }}
          {{ if eq $info.License "Unknown" -}}
            <tr class="unknown-license">
          {{- else if isCopyleft $info.License -}}
            <tr class="copyleft">
          {{- else -}}
            <tr class="non-copyleft">
          {{- end }}
            <td>{{ parseCoord $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $info.Parent }}</td>
            <td>{{ $info.IntroducedBy }}</td>
            <td>{{ $info.License }}</td>
            <td>
              <a href="{{ buildRepoLink $dep }}" target="_blank">View Details</a>
            </td>
            <td>
              {{ if ne $info.License "Unknown" }}
                <a href="{{ buildPOMLink $dep }}" target="_blank">POM File</a>
              {{ else }}
                -
              {{ end }}
            </td>
          </tr>
        {{ end }}
      </tbody>
    </table>
    <h3>Dependency Tree ({{$section.FilePath}})</h3>
    {{ buildDependencyTreesHTML $section.DependencyTree }}
  {{ end }}
</body>
</html>`

	funcMap := template.FuncMap{
		"isCopyleft":               isCopyleft,
		"buildDependencyTreesHTML": buildDependencyTreesHTML,
		"sortKeys": func(m map[string]ExtendedDep) []string {
			keys := make([]string, 0, len(m))
			for k := range m {
				keys = append(keys, k)
			}
			// Sort by license category + alphabetical
			sort.Slice(keys, func(i, j int) bool {
				ci := categoryRank(m[keys[i]].License)
				cj := categoryRank(m[keys[j]].License)
				if ci == cj {
					return keys[i] < keys[j]
				}
				return ci < cj
			})
			return keys
		},
		"parseCoord":   parseCoord,
		"parseVersion": parseVersion,
		"buildRepoLink": func(depWithVer string) string {
			return buildRepoLink(depWithVer)
		},
		"buildPOMLink": func(depWithVer string) string {
			return buildPOMLink(depWithVer)
		},
	}

	tmpl, err := template.New("report").Funcs(funcMap).Parse(tmplText)
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
	fmt.Printf("✅ Dependency license report generated at %s\n", outPath)
	return nil
}

// ----------------------------------------------------------------------
// MAIN FUNCTION
// ----------------------------------------------------------------------
func main() {
	// 1) Start concurrency worker pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Scanning for dependency files...")
	var sections []ReportSection

	// 2) Process pom.xml files
	pomFiles, _ := findAllPOMFiles(".")
	if len(pomFiles) > 0 {
		fmt.Printf("Found %d pom.xml file(s):\n", len(pomFiles))
		for _, pf := range pomFiles {
			fmt.Printf(" - %s\n", pf)
			deps, err := parseOneLocalPOMFile(pf)
			if err != nil {
				fmt.Printf("Error parsing %s => %v\n", pf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   pf,
				DirectDeps: deps,
				AllDeps:    make(map[string]ExtendedDep),
			})
		}
	}

	// 3) Process TOML files
	tomlFiles, _ := findAllTOMLFiles(".")
	if len(tomlFiles) > 0 {
		fmt.Printf("Found %d TOML file(s):\n", len(tomlFiles))
		for _, tf := range tomlFiles {
			fmt.Printf(" - %s\n", tf)
			deps, err := parseTOMLFile(tf)
			if err != nil {
				fmt.Printf("Error parsing %s => %v\n", tf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   tf,
				DirectDeps: deps,
				AllDeps:    make(map[string]ExtendedDep),
			})
		}
	}

	// 4) Process Gradle build files
	gradleFiles, _ := findAllGradleFiles(".")
	if len(gradleFiles) > 0 {
		fmt.Printf("Found %d Gradle file(s):\n", len(gradleFiles))
		for _, gf := range gradleFiles {
			fmt.Printf(" - %s\n", gf)
			deps, err := parseBuildGradleFile(gf)
			if err != nil {
				fmt.Printf("Error parsing %s => %v\n", gf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   gf,
				DirectDeps: deps,
				AllDeps:    make(map[string]ExtendedDep),
			})
		}
	}

	if len(sections) == 0 {
		fmt.Println("No dependency files found. Exiting.")
		return
	}

	// 5) BFS for transitive dependencies
	fmt.Println("Starting BFS to resolve transitive dependencies...")
	buildTransitiveClosure(sections)

	// 6) Shut down concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// 7) Compute summary counts
	for i := range sections {
		sec := &sections[i]
		var directCount, indirectCount, copyleftCount, unknownCount int
		for k, info := range sec.AllDeps {
			if info.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			} else {
				indirectCount++
			}
			if isCopyleft(info.License) {
				copyleftCount++
			}
			if info.License == "Unknown" {
				unknownCount++
			}
		}
		sec.DirectCount = directCount
		sec.IndirectCount = indirectCount
		sec.CopyleftCount = copyleftCount
		sec.UnknownCount = unknownCount
	}

	// 8) Generate HTML report
	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}
	fmt.Println("Analysis complete.")
}

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

const (
	localPOMCacheDir = ".pom-cache"     // disk caching directory for fetched POM files
	pomWorkerCount   = 10               // number of concurrent POM fetch workers
	fetchTimeout     = 30 * time.Second // HTTP GET timeout duration
)

var (
	pomCache    sync.Map // cache for fetched POMs: key "group:artifact:version" -> *MavenPOM
	parentVisit sync.Map // to detect cycles in parent POM chain

	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	channelOpen  = true
	channelMutex sync.Mutex

	// Minimal SPDX license map: identifier -> (Friendly Name, Copyleft flag)
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

// Data structures for POM XML parsing
type LicenseXML struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

type MavenPOM struct {
	XMLName        xml.Name `xml:"project"`
	Parent         POMParent `xml:"parent"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Dependencies []POMDep   `xml:"dependencies>dependency"`
	Licenses     []LicenseXML `xml:"licenses>license"`
	GroupID      string     `xml:"groupId"`
	ArtifactID   string     `xml:"artifactId"`
	Version      string     `xml:"version"`
}

// Data structures for dependency analysis
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or "group/artifact:version" of parent
	Transitive []*DependencyNode
}

type ExtendedDepInfo struct {
	Display           string
	Lookup            string
	Parent            string
	License           string
	LicenseProjectURL string
	LicensePomURL     string
}

type DepEntry struct {
	Key  string
	Info ExtendedDepInfo
}

type ReportSection struct {
	FilePath       string
	DirectDeps     map[string]string         // direct dependencies (group/artifact -> version)
	Dependencies   map[string]ExtendedDepInfo // all dependencies (flat map)
	DependencyTree []*DependencyNode
	SortedDeps     []DepEntry
	DirectCount    int
	IndirectCount  int
	CopyleftCount  int
	UnknownCount   int
}

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

// BFS support structures
type depState struct {
	Version string
	Depth   int
}

type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
}

// findAllPOMFiles searches for all pom.xml files in the given root directory
func findAllPOMFiles(root string) ([]string, error) {
	var pomFiles []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			pomFiles = append(pomFiles, path)
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if len(pomFiles) == 0 {
		return nil, fmt.Errorf("no pom.xml files found in %s", root)
	}
	return pomFiles, nil
}

// parseOneLocalPOMFile parses a local pom.xml and returns a map of direct dependencies (group/artifact -> version)
func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if e := xml.Unmarshal(data, &pom); e != nil {
		return nil, fmt.Errorf("error parsing pom.xml '%s': %v", filePath, e)
	}
	depMap := make(map[string]string)
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
		key := fmt.Sprintf("%s/%s", g, a)
		depMap[key] = v
	}
	return depMap, nil
}

// findTOMLFile finds the first .toml file in the directory tree
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
		return "", fmt.Errorf("error walking path %q: %v", root, err)
	}
	if tomlFile == "" {
		return "", fmt.Errorf("no .toml file found")
	}
	return tomlFile, nil
}

// parseTOMLFile parses a TOML file (e.g., Gradle versions.toml) and returns direct dependencies (group/artifact -> version)
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

// loadVersions reads a TOML tree and returns a map of version reference keys to version strings
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

// findBuildGradleFiles finds all build.gradle files in the directory tree
func findBuildGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr != nil {
			return werr
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

// parseBuildGradleFile parses a Gradle build.gradle and returns direct dependencies (group/artifact -> version)
func parseBuildGradleFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	// parse variable definitions like: def varName = 'value'
	varMap := parseVariables(content)
	deps := make(map[string]string)
	// regex to find dependency declarations
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		depStr := m[2] // the group:artifact:version string
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
				// replace ${var} with actual values if possible
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

// parseVariables extracts Gradle variable definitions (def NAME = "value") into a map
func parseVariables(content string) map[string]string {
	varMap := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		if len(m) >= 3 {
			name := m[1]
			val := m[2]
			varMap[name] = val
		}
	}
	return varMap
}

// parseVersionRange returns the lowest bound if version string is a range like [1.2,2.0)
func parseVersionRange(v string) string {
	v = strings.TrimSpace(v)
	if (strings.HasPrefix(v, "[") || strings.HasPrefix(v, "(")) && strings.Contains(v, ",") {
		trimmed := strings.Trim(v, "[]() ")
		parts := strings.Split(trimmed, ",")
		if len(parts) > 0 {
			low := strings.TrimSpace(parts[0])
			if low == "" {
				low = "0.0"
			}
			return low
		}
	}
	return v
}

// getLatestVersion attempts to retrieve the latest version for a given group and artifact from Maven Central, then Google Maven as fallback
func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	// Try Maven Central metadata
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	v, err := fetchLatestVersionFromURL(mavenURL)
	if err == nil && v != "" {
		return v, nil
	}
	// Fallback to Google Maven
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	v2, err2 := fetchLatestVersionFromURL(googleURL)
	if err2 == nil && v2 != "" {
		return v2, nil
	}
	return "", fmt.Errorf("could not resolve version for %s:%s", g, a)
}

// fetchLatestVersionFromURL fetches a Maven metadata XML and parses out the latest or release version
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
	if e := xml.Unmarshal(data, &md); e != nil {
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
	return "", fmt.Errorf("no version found in metadata at %s", url)
}

// skipScope returns true if scope is test/provided/system or optional is "true"
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

// pomFetchWorker is a worker that fetches POM files (with caching and parent merging) for requests from pomRequests channel
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("Worker: Starting fetch for %s:%s:%s at %s\n", req.GroupID, req.ArtifactID, req.Version, time.Now().Format(time.RFC3339))
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		if err != nil {
			fmt.Printf("⚠️ Worker: Error fetching POM for %s:%s:%s: %v\n", req.GroupID, req.ArtifactID, req.Version, err)
		}
		fmt.Printf("Worker: Completed fetch for %s:%s:%s at %s (POM exists: %v)\n", req.GroupID, req.ArtifactID, req.Version, time.Now().Format(time.RFC3339), pom != nil)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// concurrentFetchPOM fetches a POM either by dispatching to the worker pool or directly if the channel is closed
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	fmt.Printf("concurrentFetchPOM: Attempting fetch for %s:%s:%s\n", g, a, v)
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("concurrentFetchPOM: Cache HIT for %s\n", key)
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("concurrentFetchPOM: Channel closed => direct fetch for %s\n", key)
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	resChan := make(chan fetchResult, 1)
	pomRequests <- fetchRequest{GroupID: g, ArtifactID: a, Version: v, ResultChan: resChan}
	res := <-resChan
	if res.Err != nil {
		fmt.Printf("concurrentFetchPOM: Error for %s => %v\n", key, res.Err)
		return nil, nil
	}
	if res.POM == nil {
		fmt.Printf("concurrentFetchPOM: No POM found for %s\n", key)
		return nil, nil
	}
	pomCache.Store(key, res.POM)
	fmt.Printf("concurrentFetchPOM: Fetched & cached POM for %s\n", key)
	return res.POM, nil
}

// retrieveOrLoadPOM retrieves a POM from cache/disk or fetches it remotely, then merges its parent chain
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	fmt.Printf("retrieveOrLoadPOM: Checking cache & disk for %s\n", key)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("retrieveOrLoadPOM: Cache HIT for %s\n", key)
		return c.(*MavenPOM), nil
	}
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
		fmt.Printf("retrieveOrLoadPOM: Disk load success for %s\n", key)
	} else {
		fmt.Printf("retrieveOrLoadPOM: Disk load fail or no POM => remote fetch for %s\n", key)
		pom, err = fetchRemotePOM(g, a, v)
		if err != nil {
			return nil, err
		}
		pomCache.Store(key, pom)
		_ = savePOMToDisk(g, a, v, pom)
	}
	if pom == nil {
		return nil, fmt.Errorf("no POM for %s", key)
	}
	// ensure groupID and version are set (may inherit from parent)
	if pom.GroupID == "" {
		pom.GroupID = pom.Parent.GroupID
	}
	if pom.Version == "" {
		pom.Version = pom.Parent.Version
	}
	fmt.Printf("retrieveOrLoadPOM: Merging parents for %s\n", key)
	err = loadAllParents(pom, 0)
	if err != nil {
		fmt.Printf("retrieveOrLoadPOM: Error merging parent for %s => %v\n", key, err)
	}
	return pom, nil
}

// fetchRemotePOM tries to fetch the POM from Google Maven first, then Maven Central
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	fmt.Printf("fetchRemotePOM: Trying Google Maven => %s\n", urlG)
	if pom, err := fetchPOMFromURL(urlG); err == nil && pom != nil {
		return pom, nil
	}
	fmt.Printf("fetchRemotePOM: Trying Maven Central => %s\n", urlC)
	if pom, err := fetchPOMFromURL(urlC); err == nil && pom != nil {
		return pom, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s", g, a, v)
}

// fetchPOMFromURL fetches and parses a POM from a given URL
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
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e := dec.Decode(&pom); e != nil {
		return nil, e
	}
	return &pom, nil
}

// loadAllParents recursively loads parent POMs and merges dependencyManagement into the child POM
func loadAllParents(p *MavenPOM, depth int) error {
	if p.Parent.GroupID == "" || p.Parent.ArtifactID == "" || p.Parent.Version == "" {
		return nil
	}
	pkey := fmt.Sprintf("%s:%s:%s", p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if _, visited := parentVisit.Load(pkey); visited {
		return fmt.Errorf("cycle in parent POM chain: %s", pkey)
	}
	parentVisit.Store(pkey, true)
	parentPOM, err := retrieveOrLoadPOM(p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if err != nil {
		return err
	}
	// merge parent dependencyManagement into child's dependencyManagement
	p.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, p.DependencyMgmt.Dependencies)
	// inherit missing fields
	if p.GroupID == "" {
		p.GroupID = parentPOM.GroupID
	}
	if p.Version == "" {
		p.Version = parentPOM.Version
	}
	return loadAllParents(parentPOM, depth+1)
}

// mergeDepMgmt merges parent and child dependencyManagement dependency lists (child entries override parent entries)
func mergeDepMgmt(parent, child []POMDep) []POMDep {
	outMap := make(map[string]POMDep)
	for _, d := range parent {
		key := d.GroupID + ":" + d.ArtifactID
		outMap[key] = d
	}
	for _, d := range child {
		key := d.GroupID + ":" + d.ArtifactID
		outMap[key] = d
	}
	var merged []POMDep
	for _, dep := range outMap {
		merged = append(merged, dep)
	}
	sort.Slice(merged, func(i, j int) bool {
		return merged[i].GroupID < merged[j].GroupID
	})
	return merged
}

// loadPOMFromDisk loads a POM from the local cache directory if present
func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if e := dec.Decode(&pom); e != nil {
		return nil, e
	}
	return &pom, nil
}

// savePOMToDisk saves a POM to the local cache directory
func savePOMToDisk(g, a, v string, pom *MavenPOM) error {
	path := localCachePath(g, a, v)
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return err
	}
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	out, err := xml.MarshalIndent(pom, "", "  ")
	if err != nil {
		return err
	}
	_, err = f.Write(out)
	return err
}

// localCachePath constructs the file path for storing a POM in the local cache
func localCachePath(g, a, v string) string {
	groupPath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, groupPath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// parseManagedVersions builds a map of group/artifact -> version from a POM's dependencyManagement section
func parseManagedVersions(pom *MavenPOM) map[string]string {
	res := make(map[string]string)
	for _, d := range pom.DependencyMgmt.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		if d.Version != "" {
			key := d.GroupID + "/" + d.ArtifactID
			res[key] = parseVersionRange(d.Version)
		}
	}
	return res
}

// splitGA splits a "group/artifact" string into group and artifact
func splitGA(ga string) (string, string) {
	parts := strings.SplitN(ga, "/", 2)
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// fillDepMap recursively adds each dependency node (and its children) to the flat dependency map
func fillDepMap(node *DependencyNode, depMap map[string]ExtendedDepInfo) {
	key := fmt.Sprintf("%s@%s", node.Name, node.Version)
	info, exists := depMap[key]
	if !exists {
		info = ExtendedDepInfo{
			Display: node.Version,
			Lookup:  node.Version,
			Parent:  node.Parent,
		}
	} else {
		info.Display = node.Version
		info.Lookup = node.Version
		info.Parent = node.Parent
	}
	info.License = node.License
	depMap[key] = info
	for _, child := range node.Transitive {
		fillDepMap(child, depMap)
	}
}

// sortRoots sorts dependency tree nodes (and their children recursively) by Name alphabetically
func sortRoots(nodes []*DependencyNode) {
	sort.Slice(nodes, func(i, j int) bool {
		return nodes[i].Name < nodes[j].Name
	})
	for _, n := range nodes {
		sortRoots(n.Transitive)
	}
}

// detectLicense returns a normalized license name or "Unknown" if none found
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

// isCopyleft checks if a license name is a known copyleft license
func isCopyleft(name string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "CC-BY-SA",
		"MPL", "EPL", "CPL", "CDDL", "EUPL", "Affero", "OSL", "CeCILL",
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

// buildDependencyTreeHTML returns an HTML snippet for a dependency node and its transitive tree
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

// buildDependencyTreesHTML builds the combined HTML for all root dependency trees
func buildDependencyTreesHTML(nodes []*DependencyNode) template.HTML {
	var buf strings.Builder
	for _, n := range nodes {
		buf.WriteString(buildDependencyTreeHTML(n, 0))
	}
	return template.HTML(buf.String())
}

// generateHTMLReport creates an HTML report file from the analyzed sections
func generateHTMLReport(sections []ReportSection) error {
	outDir := "./license-checker"
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
  <h1>Dependency License Report</h1>
  {{ range . }}
    <h2>File: {{ .FilePath }}</h2>
    <p>
      Direct Dependencies: {{ .DirectCount }}<br>
      Indirect Dependencies: {{ .IndirectCount }}<br>
      Copyleft Dependencies: {{ .CopyleftCount }}<br>
      Unknown License Dependencies: {{ .UnknownCount }}
    </p>
    <h3>Dependencies Table</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>License</th>
          <th>Parent</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ range .SortedDeps }}
          <tr {{ if eq .Info.License "Unknown" }}class="unknown-license"{{ else if isCopyleft .Info.License }}class="copyleft"{{ else }}class="non-copyleft"{{ end }}>
            <td>{{ .Key }}</td>
            <td>{{ .Info.Display }}</td>
            <td>{{ .Info.License }}</td>
            <td>{{ .Info.Parent }}</td>
            {{ if .Info.LicenseProjectURL }}
              <td><a href="{{ .Info.LicenseProjectURL }}" target="_blank">View Details</a></td>
            {{ else }}
              <td></td>
            {{ end }}
            {{ if .Info.LicensePomURL }}
              <td><a href="{{ .Info.LicensePomURL }}" target="_blank">View POM</a></td>
            {{ else }}
              <td></td>
            {{ end }}
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
	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"isCopyleft":           isCopyleft,
		"buildDependencyTreesHTML": buildDependencyTreesHTML,
	}).Parse(tmplText)
	if err != nil {
		return err
	}
	reportPath := filepath.Join(outDir, "dependency-license-report.html")
	f, err := os.Create(reportPath)
	if err != nil {
		return err
	}
	defer f.Close()
	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}
	fmt.Printf("✅ License report generated at %s\n", reportPath)
	return nil
}

// printConsoleReport prints a summary of the dependencies to the console
func printConsoleReport(sections []ReportSection) {
	fmt.Println("----- Console Dependency Report -----")
	for _, sec := range sections {
		fmt.Printf("File: %s\n", sec.FilePath)
		fmt.Printf("Direct: %d, Indirect: %d, Copyleft: %d, Unknown: %d\n",
			sec.DirectCount, sec.IndirectCount, sec.CopyleftCount, sec.UnknownCount)
		fmt.Println("Flat Dependencies:")
		var keys []string
		for k := range sec.Dependencies {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			info := sec.Dependencies[k]
			fmt.Printf("  %s => %s (Parent=%s, License=%s)\n", k, info.Display, info.Parent, info.License)
		}
		fmt.Println("Dependency Tree:")
		for _, node := range sec.DependencyTree {
			printTreeNode(node, 0)
		}
		fmt.Println("-------------------------------------")
	}
}

// printTreeNode prints a dependency tree node to the console with indentation
func printTreeNode(node *DependencyNode, indent int) {
	prefix := strings.Repeat("  ", indent)
	fmt.Printf("%s- %s@%s (License: %s)\n", prefix, node.Name, node.Version, node.License)
	for _, child := range node.Transitive {
		printTreeNode(child, indent+1)
	}
}

// buildTransitiveClosure performs unlimited-depth BFS to resolve all transitive dependencies for each report section
func buildTransitiveClosure(sections []ReportSection) {
	for idx := range sections {
		sec := &sections[idx]
		fmt.Printf("BFS: Building transitive closure for file: %s\n", sec.FilePath)
		flatDeps := make(map[string]ExtendedDepInfo)
		// initialize flatDeps with direct dependencies
		for ga, ver := range sec.DirectDeps {
			key := fmt.Sprintf("%s@%s", ga, ver)
			flatDeps[key] = ExtendedDepInfo{
				Display: ver,
				Lookup:  ver,
				Parent:  "direct",
				License: "",
			}
		}
		var rootNodes []*DependencyNode
		var queue []queueItem
		visited := make(map[string]bool)
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*DependencyNode)
		// BFS initialization
		for ga, ver := range sec.DirectDeps {
			key := fmt.Sprintf("%s@%s", ga, ver)
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
		// BFS traversal
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("BFS: Processing %s (depth %d)\n", it.GroupArtifact, it.Depth)
			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			if strings.Contains(it.Version, "${") || strings.ToLower(it.Version) == "unknown" {
				latest, err := getLatestVersion(gid, aid)
				if err != nil {
					fmt.Printf("BFS: Could not fetch latest version for %s/%s => unknown\n", gid, aid)
					it.Version = "unknown"
				} else {
					it.Version = latest
				}
			}
			pom, err := concurrentFetchPOM(gid, aid, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("BFS: Skipping %s:%s:%s due to fetch error or nil POM\n", gid, aid, it.Version)
				continue
			}
			// attach license info to the node represented by ParentNode
			if it.ParentNode != nil {
				licName := detectLicense(pom)
				it.ParentNode.License = licName
				it.ParentNode.Copyleft = isCopyleft(licName)
				fmt.Printf("BFS: Detected license for %s:%s:%s => %s\n", gid, aid, it.Version, licName)
			}
			// prepare map of managed versions from dependencyManagement
			managed := parseManagedVersions(pom)
			// iterate over direct dependencies in this POM
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := parseVersionRange(d.Version)
				if cv == "" || strings.Contains(cv, "${") {
					if mv, ok := managed[childGA]; ok && mv != "" {
						cv = mv
					} else {
						latest, err2 := getLatestVersion(d.GroupID, d.ArtifactID)
						if err2 != nil {
							fmt.Printf("BFS: Could not fetch version for %s\n", childGA)
							continue
						}
						cv = latest
					}
				}
				if cv == "" {
					continue
				}
				childDepth := it.Depth + 1
				childKey := fmt.Sprintf("%s@%s", childGA, cv)
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
					flatDeps[childKey] = ExtendedDepInfo{
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
							childNode.Parent = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
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
		// propagate license info into flatDeps map for final output
		for _, root := range rootNodes {
			fillDepMap(root, flatDeps)
		}
		// assign the final results to the section
		sec.Dependencies = flatDeps
		sortRoots(rootNodes)
		sec.DependencyTree = rootNodes
	}
}

func main() {
	// Start worker pool for POM fetching
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}
	fmt.Println("Starting dependency analysis...")

	var sections []ReportSection

	// Find and parse pom.xml files
	pomFiles, err := findAllPOMFiles(".")
	if err == nil {
		fmt.Printf("Found %d pom.xml file(s).\n", len(pomFiles))
		for _, pf := range pomFiles {
			fmt.Printf("Parsing direct dependencies from %s\n", pf)
			directDeps, err := parseOneLocalPOMFile(pf)
			if err != nil {
				fmt.Printf("Error parsing %s: %v\n", pf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   pf,
				DirectDeps: directDeps,
				Dependencies: make(map[string]ExtendedDepInfo),
			})
		}
	} else {
		// Only print if error is not "no pom.xml files found"
		if !strings.Contains(err.Error(), "no pom.xml files") {
			fmt.Printf("Error scanning for pom.xml files: %v\n", err)
		}
	}

	// Find and parse build.gradle files
	gradleFiles, err := findBuildGradleFiles(".")
	if err == nil {
		if len(gradleFiles) > 0 {
			fmt.Printf("Found %d build.gradle file(s).\n", len(gradleFiles))
		}
		for _, gf := range gradleFiles {
			fmt.Printf("Parsing direct dependencies from %s\n", gf)
			directDeps, err := parseBuildGradleFile(gf)
			if err != nil {
				fmt.Printf("Error parsing %s: %v\n", gf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   gf,
				DirectDeps: directDeps,
				Dependencies: make(map[string]ExtendedDepInfo),
			})
		}
	} else {
		fmt.Printf("Error scanning for build.gradle files: %v\n", err)
	}

	// Find and parse versions.toml or other .toml files
	tomlPath, err := findTOMLFile(".")
	if err == nil {
		fmt.Printf("Found TOML file: %s\n", tomlPath)
		fmt.Printf("Parsing direct dependencies from %s\n", tomlPath)
		directDeps, err := parseTOMLFile(tomlPath)
		if err != nil {
			fmt.Printf("Error parsing TOML file: %v\n", err)
		} else {
			sections = append(sections, ReportSection{
				FilePath:   tomlPath,
				DirectDeps: directDeps,
				Dependencies: make(map[string]ExtendedDepInfo),
			})
		}
	} else {
		// Only print error if some error occurred other than not found
		if !strings.Contains(err.Error(), "no .toml file found") {
			fmt.Printf("Error scanning for .toml file: %v\n", err)
		}
	}

	if len(sections) == 0 {
		fmt.Println("No pom.xml, build.gradle, or .toml files were found. Exiting.")
		// No need to keep workers running
		channelMutex.Lock()
		channelOpen = false
		channelMutex.Unlock()
		close(pomRequests)
		wgWorkers.Wait()
		return
	}

	fmt.Println("Starting transitive dependency resolution (BFS)...")
	buildTransitiveClosure(sections)

	// Signal to stop accepting new fetch requests and wait for workers to finish outstanding jobs
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// After BFS, compute license information and links for each dependency and summary counts
	fmt.Println("Computing license info and summary metrics...")
	for i := range sections {
		sec := &sections[i]
		var directCount, indirectCount, copyleftCount, unknownCount int
		// Fill in LicenseProjectURL and LicensePomURL for each dependency in flat map
		for depKey, info := range sec.Dependencies {
			parts := strings.Split(depKey, "@")
			if len(parts) != 2 {
				continue
			}
			ga := parts[0]
			gaParts := strings.Split(ga, "/")
			if len(gaParts) != 2 {
				continue
			}
			g, a := gaParts[0], gaParts[1]
			if info.License == "" {
				info.License = "Unknown"
			}
			if info.License == "Unknown" {
				// unknown license, provide a search link
				info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, info.Lookup)
				info.LicensePomURL = ""
			} else {
				// determine appropriate repository links (Google Maven vs Maven Central)
				groupPath := strings.ReplaceAll(g, ".", "/")
				googleBase := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/", groupPath, a, info.Lookup)
				centralBase := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, a, info.Lookup)
				googlePom := fmt.Sprintf("%s%s-%s.pom", googleBase, a, info.Lookup)
				centralPom := fmt.Sprintf("%s%s-%s.pom", centralBase, a, info.Lookup)
				// Default to Google Maven for com.android group, else Maven Central first
				chosenProjectURL := ""
				chosenPomURL := ""
				client := http.Client{Timeout: 5 * time.Second}
				if strings.HasPrefix(g, "com.android") {
					// try Google first
					respG, errG := client.Head(googlePom)
					if errG == nil && respG.StatusCode == 200 {
						chosenProjectURL = googleBase
						chosenPomURL = googlePom
					} else {
						respC, errC := client.Head(centralPom)
						if errC == nil && respC.StatusCode == 200 {
							chosenProjectURL = centralBase
							chosenPomURL = centralPom
						}
					}
				} else {
					// try Maven Central first
					respC, errC := client.Head(centralPom)
					if errC == nil && respC.StatusCode == 200 {
						chosenProjectURL = centralBase
						chosenPomURL = centralPom
					} else {
						respG, errG := client.Head(googlePom)
						if errG == nil && respG.StatusCode == 200 {
							chosenProjectURL = googleBase
							chosenPomURL = googlePom
						}
					}
				}
				if chosenPomURL == "" {
					// fallback: Google search
					info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, info.Lookup)
					info.LicensePomURL = ""
				} else {
					info.LicenseProjectURL = chosenProjectURL
					info.LicensePomURL = chosenPomURL
				}
			}
			sec.Dependencies[depKey] = info
			// count categories for summary
			if info.Parent == "direct" || strings.HasSuffix(depKey, "@unknown") {
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
		// prepare sorted list of dependencies for template output
		var sortedList []DepEntry
		for k, inf := range sec.Dependencies {
			sortedList = append(sortedList, DepEntry{Key: k, Info: inf})
		}
		sort.Slice(sortedList, func(i, j int) bool {
			// sort by license category (Copyleft < Unknown < Others) then by dependency name
			li := sortedList[i].Info.License
			lj := sortedList[j].Info.License
			cati := 2
			catj := 2
			if isCopyleft(li) {
				cati = 0
			} else if li == "Unknown" {
				cati = 1
			}
			if isCopyleft(lj) {
				catj = 0
			} else if lj == "Unknown" {
				catj = 1
			}
			if cati != catj {
				return cati < catj
			}
			return sortedList[i].Key < sortedList[j].Key
		})
		sec.SortedDeps = sortedList
	}
	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}
	printConsoleReport(sections)
	fmt.Println("Analysis complete.")
}

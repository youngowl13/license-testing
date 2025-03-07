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
// CONFIG
// ----------------------------------------------------------------------
const (
	localPOMCacheDir = ".pom-cache"     
	pomWorkerCount   = 10               
	fetchTimeout     = 30 * time.Second 
	outputReport     = "license-checker/dependency-license-report.html"
)

// ----------------------------------------------------------------------
// GLOBALS
// ----------------------------------------------------------------------
var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map 
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// CONCURRENCY TYPES
// ----------------------------------------------------------------------
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

// fetchResult now carries the actual URL used (UsedURL).
type fetchResult struct {
	POM     *MavenPOM
	UsedURL string 
	Err     error
}

// ----------------------------------------------------------------------
// SPDX LICENSE MAP
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

// License, POMDep, MavenPOM are same as before
type License struct {
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

type MavenPOM struct {
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
	XMLName xml.Name `xml:"project"`
}

// BFS node
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string 
	Transitive []*DependencyNode

	UsedPOMURL string 
}

// ExtendedDep for final table
type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string 
}

// ReportSection for each discovered file
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string      
	AllDeps         map[string]ExtendedDep 
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

func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if e := xml.Unmarshal(data, &pom); e != nil {
		return nil, fmt.Errorf("error parsing pom.xml '%s': %v", filePath, e)
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
	libTree := tree.Get("libraries")
	if libTree == nil {
		return nil, fmt.Errorf("TOML lacks 'libraries' table")
	}
	libraries, ok := libTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' is not a valid TOML table")
	}
	for _, k := range libraries.Keys() {
		val := libraries.Get(k)
		sub, ok := val.(*toml.Tree)
		if !ok {
			continue
		}
		module, _ := sub.Get("module").(string)
		versionRef, _ := sub.Get("version.ref").(string)
		if module == "" || versionRef == "" {
			continue
		}
		verVal := versions[versionRef]
		if verVal == "" {
			verVal = "unknown"
		}
		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		key := g + "/" + a
		deps[key] = verVal
	}
	return deps, nil
}

func loadVersions(tree *toml.Tree) (map[string]string, error) {
	versions := make(map[string]string)
	vObj := tree.Get("versions")
	if vObj == nil {
		return versions, nil
	}
	vMap, ok := vObj.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'versions' is not a valid TOML table")
	}
	for _, k := range vMap.Keys() {
		val := vMap.Get(k)
		if str, ok := val.(string); ok {
			versions[k] = str
		}
	}
	return versions, nil
}

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
					if v, ok := varMap[inner]; ok {
						return v
					}
					return ""
				})
				if version == "" {
					version = "unknown"
				}
			}
		}
		key := group + "/" + artifact
		deps[key] = version
	}
	return deps, nil
}

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
// BFS + LICENSE FETCH
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

// fetchRemotePOM => returns *MavenPOM + usedURL
func fetchRemotePOM(group, artifact, version string) (*MavenPOM, string, error) {
	groupPath := strings.ReplaceAll(group, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	client := http.Client{Timeout: fetchTimeout}

	fmt.Printf("[FETCH-REMOTE] Attempt central => %s\n", urlCentral)
	resp, err := client.Get(urlCentral)
	if err == nil && resp.StatusCode == 200 {
		defer resp.Body.Close()
		data, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, "", err
		}
		var pom MavenPOM
		if e := xml.Unmarshal(data, &pom); e != nil {
			return nil, "", e
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from central => %s:%s:%s\n", group, artifact, version)
		return &pom, urlCentral, nil
	}
	if resp != nil {
		resp.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] Attempt google => %s\n", urlGoogle)
	resp2, err2 := client.Get(urlGoogle)
	if err2 == nil && resp2.StatusCode == 200 {
		defer resp2.Body.Close()
		data, err := io.ReadAll(resp2.Body)
		if err != nil {
			return nil, "", err
		}
		var pom MavenPOM
		if e := xml.Unmarshal(data, &pom); e != nil {
			return nil, "", e
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from google => %s:%s:%s\n", group, artifact, version)
		return &pom, urlGoogle, nil
	}
	if resp2 != nil {
		resp2.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] FAILED => %s:%s:%s\n", group, artifact, version)
	return nil, "", fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

// concurrentFetchPOM => returns *MavenPOM + usedURL in the fetchResult
func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, string, error) {
	key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
	if cached, ok := pomCache.Load(key); ok {
		fmt.Printf("[CACHE] HIT => %s\n", key)
		// We'll store just the POM in cache, not the usedURL, so we might not have the actual usedURL from cache.
		// If you want to store usedURL too, you can store a struct in the cache. 
		return cached.(*MavenPOM), "", nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("[FETCH] channel closed => direct => %s\n", key)
		pom, urlUsed, err := fetchRemotePOM(group, artifact, version)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, urlUsed, err
	}
	req := fetchRequest{
		GroupID:    group,
		ArtifactID: artifact,
		Version:    version,
		ResultChan: make(chan fetchResult, 1),
	}
	fmt.Printf("[FETCH] Enqueue => %s\n", key)
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.UsedURL, res.Err
}

// pomFetchWorker => returns usedURL as well
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		key := fmt.Sprintf("%s:%s:%s", req.GroupID, req.ArtifactID, req.Version)
		fmt.Printf("[WORKER] fetch => %s\n", key)
		pom, usedURL, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, UsedURL: usedURL, Err: err}
	}
}

// buildTransitiveClosure => BFS
func buildTransitiveClosure(sections []ReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("[BFS] For file => %s\n", sec.FilePath)
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
				PomURL:       "",
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

		for ga, ver := range sec.DirectDeps {
			k := ga + "@" + ver
			visited[k] = true
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

		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("[BFS] %s@%s (depth=%d)\n", it.GroupArtifact, it.Version, it.Depth)
			group, artifact := splitGA(it.GroupArtifact)
			if group == "" || artifact == "" {
				continue
			}
			if strings.ToLower(it.Version) == "unknown" {
				continue
			}
			pom, usedURL, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				continue
			}
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
				it.ParentNode.UsedPOMURL = usedURL // store actual used URL
			}
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
					PomURL:       "", 
				}
				it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
				queue = append(queue, queueItem{
					GroupArtifact: childGA,
					Version:       cv,
					Depth:         it.Depth + 1,
					ParentNode:    childNode,
				})
			}
		}
		// fill BFS
		for _, root := range rootNodes {
			fillDepMap(root, allDeps)
		}
		// set top-level
		for _, root := range rootNodes {
			rootCoord := fmt.Sprintf("%s:%s", root.Name, root.Version)
			setIntroducedBy(root, rootCoord, allDeps)
		}
		sec.AllDeps = allDeps
		sec.DependencyTree = rootNodes
	}
}

func fillDepMap(node *DependencyNode, all map[string]ExtendedDep) {
	key := node.Name + "@" + node.Version
	info, ok := all[key]
	if !ok {
		info = ExtendedDep{
			Display: node.Version,
			Lookup:  node.Version,
			Parent:  node.Parent,
			PomURL:  node.UsedPOMURL,
		}
	} else {
		if node.UsedPOMURL != "" {
			info.PomURL = node.UsedPOMURL
		}
	}
	if node.License == "" {
		info.License = "Unknown"
	} else {
		info.License = node.License
	}
	all[key] = info

	for _, c := range node.Transitive {
		fillDepMap(c, all)
	}
}

func setIntroducedBy(node *DependencyNode, rootCoord string, all map[string]ExtendedDep) {
	for _, child := range node.Transitive {
		key := child.Name + "@" + child.Version
		inf := all[key]
		inf.IntroducedBy = rootCoord
		all[key] = inf
		setIntroducedBy(child, rootCoord, all)
	}
}

// ----------------------------------------------------------------------
// HTML REPORT
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
	sort.Slice(nodes, func(i, j int) bool {
		return nodes[i].Name < nodes[j].Name
	})
	var sb strings.Builder
	for _, node := range nodes {
		sb.WriteString(buildDependencyTreeHTML(node, 0))
	}
	return template.HTML(sb.String())
}

func categoryRank(license string) int {
	if isCopyleft(license) {
		return 0
	} else if license == "Unknown" {
		return 1
	}
	return 2
}

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
          <th>Top-Level</th>
          <th>License</th>
          <th>Used POM URL</th>
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
            <td>{{ $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $info.Parent }}</td>
            <td>{{ $info.IntroducedBy }}</td>
            <td>{{ $info.License }}</td>
            <td>
              {{ if eq $info.PomURL "" }}
                -
              {{ else }}
                <a href="{{ $info.PomURL }}" target="_blank">{{ $info.PomURL }}</a>
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
// UTILITY FOR SORTING BY LICENSE, ETC
// ----------------------------------------------------------------------
func categoryRank(license string) int {
	if isCopyleft(license) {
		return 0
	} else if license == "Unknown" {
		return 1
	}
	return 2
}

// ----------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------
func main() {
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Scanning for dependency files...")
	var sections []ReportSection

	// POM
	pomFiles, _ := findAllPOMFiles(".")
	if len(pomFiles) > 0 {
		fmt.Printf("Found %d pom.xml file(s).\n", len(pomFiles))
		for _, pf := range pomFiles {
			fmt.Printf(" - %s\n", pf)
			deps, err := parseOneLocalPOMFile(pf)
			if err != nil {
				fmt.Printf("Error parse %s => %v\n", pf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   pf,
				DirectDeps: deps,
				AllDeps:    make(map[string]ExtendedDep),
			})
		}
	}

	// TOML
	tomlFiles, _ := findAllTOMLFiles(".")
	if len(tomlFiles) > 0 {
		fmt.Printf("Found %d .toml file(s).\n", len(tomlFiles))
		for _, tf := range tomlFiles {
			fmt.Printf(" - %s\n", tf)
			deps, err := parseTOMLFile(tf)
			if err != nil {
				fmt.Printf("Error parse %s => %v\n", tf, err)
				continue
			}
			sections = append(sections, ReportSection{
				FilePath:   tf,
				DirectDeps: deps,
				AllDeps:    make(map[string]ExtendedDep),
			})
		}
	}

	// Gradle
	gradleFiles, _ := findAllGradleFiles(".")
	if len(gradleFiles) > 0 {
		fmt.Printf("Found %d Gradle file(s).\n", len(gradleFiles))
		for _, gf := range gradleFiles {
			fmt.Printf(" - %s\n", gf)
			deps, err := parseBuildGradleFile(gf)
			if err != nil {
				fmt.Printf("Error parse %s => %v\n", gf, err)
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

	fmt.Println("Starting BFS to resolve transitive dependencies...")
	buildTransitiveClosure(sections)

	// Close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Summaries
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

	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML: %v\n", err)
		os.Exit(1)
	}
	fmt.Println("Analysis complete.")
}

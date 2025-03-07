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
)

// ----------------------------------------------------------------------
// GLOBALS
// ----------------------------------------------------------------------
var (
    pomRequests = make(chan fetchRequest, 50)
    wgWorkers   sync.WaitGroup

    pomCache    sync.Map
    channelOpen = true
    channelMutex sync.Mutex
)

// Minimal SPDX license map
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
    XMLName        xml.Name `xml:"project"`
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

type DependencyNode struct {
    Name       string
    Version    string
    License    string
    Copyleft   bool
    Parent     string // "direct" or "group/artifact:version"
    Transitive []*DependencyNode
}

type ExtendedDep struct {
    Display      string
    Lookup       string
    Parent       string
    License      string
    IntroducedBy string
}

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
// FILE DISCOVERY AND PARSING
// ----------------------------------------------------------------------

// findAllPOMFiles returns all pom.xml file paths under the given root directory
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
    return pomFiles, nil
}

// parseOneLocalPOMFile parses a pom.xml and returns its direct dependencies (map "group/artifact" -> version)
func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
    data, err := os.ReadFile(filePath)
    if err != nil {
        return nil, fmt.Errorf("cannot read pom.xml '%s': %v", filePath, err)
    }
    var pom MavenPOM
    if e2 := xml.Unmarshal(data, &pom); e2 != nil {
        return nil, fmt.Errorf("error parsing pom.xml '%s': %v", filePath, e2)
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

// findAllTOMLFiles returns all .toml files under the given root directory
func findAllTOMLFiles(root string) ([]string, error) {
    var tomlFiles []string
    err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
        if err != nil {
            return err
        }
        if !info.IsDir() && strings.HasSuffix(info.Name(), ".toml") {
            tomlFiles = append(tomlFiles, path)
        }
        return nil
    })
    if err != nil {
        return nil, err
    }
    return tomlFiles, nil
}

// parseTOMLFile parses a Gradle libs.versions.toml file and returns direct dependencies (map "group/artifact" -> version)
func parseTOMLFile(filePath string) (map[string]string, error) {
    dependencies := make(map[string]string)
    tree, err := toml.LoadFile(filePath)
    if err != nil {
        return nil, fmt.Errorf("error loading TOML file: %v", err)
    }
    // Load [versions] table for version references
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
        libItem := libraries.Get(libKey)
        if libItem == nil {
            continue
        }
        lib, ok := libItem.(*toml.Tree)
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
        dependencies[key] = versionVal
    }
    return dependencies, nil
}

// loadVersions loads the [versions] table from a TOML file into a map of version reference -> actual version string
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
        val := versionsMap.Get(key)
        if str, ok := val.(string); ok {
            versions[key] = str
        }
        // ignore non-string or nested values
    }
    return versions, nil
}

// findAllGradleFiles returns all build.gradle and build.gradle.kts files under the given root directory
func findAllGradleFiles(root string) ([]string, error) {
    var files []string
    err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
        if err != nil {
            return err
        }
        name := info.Name()
        if !info.IsDir() && (strings.EqualFold(name, "build.gradle") || strings.EqualFold(name, "build.gradle.kts")) {
            files = append(files, path)
        }
        return nil
    })
    if err != nil {
        return nil, err
    }
    return files, nil
}

// parseBuildGradleFile parses a Gradle build.gradle file and returns direct dependencies (map "group/artifact" -> version)
func parseBuildGradleFile(filePath string) (map[string]string, error) {
    data, err := os.ReadFile(filePath)
    if err != nil {
        return nil, err
    }
    content := string(data)
    // Capture simple variable definitions (e.g., def someVersion = "1.2.3")
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
            // Replace variable placeholders in version (e.g., ${var})
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
            if version == "" {
                version = "unknown"
            }
        }
        key := fmt.Sprintf("%s/%s", group, artifact)
        deps[key] = version
    }
    return deps, nil
}

// parseGradleVariables finds variable assignments (def VAR = "value") in Gradle file content
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

// parseVersionRange returns a concrete version if the given version string is a range (e.g., "[1.0,2.0)"),
// otherwise it returns the version string as-is.
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

// splitGA splits a "group/artifact" string into its group and artifact components.
func splitGA(ga string) (string, string) {
    parts := strings.Split(ga, "/")
    if len(parts) != 2 {
        return "", ""
    }
    return parts[0], parts[1]
}

// isCopyleft checks if a license name is recognized as a copyleft license
func isCopyleft(name string) bool {
    for spdxID, data := range spdxLicenseMap {
        if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
            return true
        }
    }
    // Check common copyleft keywords
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

// detectLicense determines a license name from a Maven POM (returns "Unknown" if none or unrecognized)
func detectLicense(pom *MavenPOM) string {
    if pom == nil || len(pom.Licenses) == 0 {
        return "Unknown"
    }
    licName := strings.TrimSpace(pom.Licenses[0].Name)
    if licName == "" {
        return "Unknown"
    }
    // Normalize license name if it matches a known SPDX identifier
    up := strings.ToUpper(licName)
    for spdxID, data := range spdxLicenseMap {
        if strings.EqualFold(licName, spdxID) || up == strings.ToUpper(spdxID) {
            return data.Name
        }
    }
    return licName
}

// fetchRemotePOM attempts to fetch a POM file from Maven Central (primary) or Google Maven (fallback)
func fetchRemotePOM(group, artifact, version string) (*MavenPOM, error) {
    groupPath := strings.ReplaceAll(group, ".", "/")
    url1 := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
    url2 := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
    client := http.Client{Timeout: fetchTimeout}
    // Try Maven Central
    resp, err := client.Get(url1)
    if err == nil && resp.StatusCode == 200 {
        defer resp.Body.Close()
        data, err := io.ReadAll(resp.Body)
        if err != nil {
            return nil, err
        }
        var pom MavenPOM
        if e := xml.Unmarshal(data, &pom); e != nil {
            return nil, e
        }
        return &pom, nil
    }
    if resp != nil {
        resp.Body.Close()
    }
    // Try Google Maven
    resp2, err2 := client.Get(url2)
    if err2 == nil && resp2.StatusCode == 200 {
        defer resp2.Body.Close()
        data, err := io.ReadAll(resp2.Body)
        if err != nil {
            return nil, err
        }
        var pom MavenPOM
        if e := xml.Unmarshal(data, &pom); e != nil {
            return nil, e
        }
        return &pom, nil
    }
    if resp2 != nil {
        resp2.Body.Close()
    }
    return nil, fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

// concurrentFetchPOM retrieves a POM using a worker pool or directly if the pool is closed
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
func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, error) {
    key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
    if c, ok := pomCache.Load(key); ok {
        return c.(*MavenPOM), nil
    }
    channelMutex.Lock()
    open := channelOpen
    channelMutex.Unlock()
    if !open {
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
    pomRequests <- req
    res := <-req.ResultChan
    if res.Err == nil && res.POM != nil {
        pomCache.Store(key, res.POM)
    }
    return res.POM, res.Err
}

// pomFetchWorker processes POM fetch requests in parallel
func pomFetchWorker() {
    defer wgWorkers.Done()
    for req := range pomRequests {
        pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
        req.ResultChan <- fetchResult{POM: pom, Err: err}
    }
}

// buildTransitiveClosure performs a BFS to resolve transitive dependencies for each section
func buildTransitiveClosure(sections []ReportSection) {
    for i := range sections {
        sec := &sections[i]
        fmt.Printf("BFS: Building transitive closure for %s\n", sec.FilePath)
        allDeps := make(map[string]ExtendedDep)
        // Add direct dependencies to map
        for ga, ver := range sec.DirectDeps {
            key := ga + "@" + ver
            allDeps[key] = ExtendedDep{
                Display: ver,
                Lookup:  ver,
                Parent:  "direct",
                License: "",
                IntroducedBy: "", // direct dep has no introducer
            }
        }
        // Initialize BFS queue with direct dependencies
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
        // BFS traversal
        for len(queue) > 0 {
            it := queue[0]
            queue = queue[1:]
            group, artifact := splitGA(it.GroupArtifact)
            if group == "" || artifact == "" {
                continue
            }
            if strings.ToLower(it.Version) == "unknown" {
                // Unknown version, cannot resolve further
                continue
            }
            pom, err := concurrentFetchPOM(group, artifact, it.Version)
            if err != nil || pom == nil {
                // Skip if POM not found or fetch error
                continue
            }
            // Set license on the current node (ParentNode corresponds to this dependency's node)
            if it.ParentNode != nil {
                lic := detectLicense(pom)
                it.ParentNode.License = lic
                it.ParentNode.Copyleft = isCopyleft(lic)
            }
            // Enqueue all child dependencies from this POM
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
                    Display: cv,
                    Lookup:  cv,
                    Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
                    License: "",
                    IntroducedBy: "", // will set after BFS
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
        // Populate AllDeps with license info from the built dependency tree
        for _, root := range rootNodes {
            fillDepMap(root, allDeps)
        }
        // Assign IntroducedBy for each transitive dependency (direct root that introduced it)
        for _, root := range rootNodes {
            rootCoord := fmt.Sprintf("%s:%s", root.Name, root.Version)
            setIntroducedBy(root, rootCoord, allDeps)
        }
        sec.AllDeps = allDeps
        sec.DependencyTree = rootNodes
    }
}

// fillDepMap updates the AllDeps map with license information from the dependency tree nodes
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

// setIntroducedBy recursively sets the IntroducedBy field for all transitive nodes under the given root
func setIntroducedBy(node *DependencyNode, rootCoord string, all map[string]ExtendedDep) {
    for _, child := range node.Transitive {
        key := child.Name + "@" + child.Version
        info := all[key]
        info.IntroducedBy = rootCoord
        all[key] = info
        setIntroducedBy(child, rootCoord, all)
    }
}

// skipScope returns true if a dependency scope should be skipped (test, provided, system) or if optional is true
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
// HTML REPORT GENERATION
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
    sb.WriteString(`</details>`)
    return sb.String()
}

func buildDependencyTreesHTML(nodes []*DependencyNode) template.HTML {
    var sb strings.Builder
    for _, node := range nodes {
        sb.WriteString(buildDependencyTreeHTML(node, 0))
    }
    return template.HTML(sb.String())
}

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
    <h3>Dependency Table ({{ .FilePath }})</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>Parent</th>
          <th>Introduced By</th>
          <th>License</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ range $dep, $info := .AllDeps }}
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
            <td><a href="https://www.google.com/search?q={{ $dep }}+license" target="_blank">Search</a></td>
            <td><a href="https://repo1.maven.org/maven2/{{ $dep }}/{{ $info.Lookup }}" target="_blank">POM?</a></td>
          </tr>
        {{ end }}
      </tbody>
    </table>
    <h3>Dependency Tree ({{ .FilePath }})</h3>
    {{ buildDependencyTreesHTML .DependencyTree }}
  {{ end }}
</body>
</html>
`
    tmpl, err := template.New("report").Funcs(template.FuncMap{
        "isCopyleft": isCopyleft,
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
    fmt.Printf("✅ Dependency license report generated at %s\n", outPath)
    return nil
}

// ----------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------
func main() {
    // Start worker pool for POM fetching
    for i := 0; i < pomWorkerCount; i++ {
        wgWorkers.Add(1)
        go pomFetchWorker()
    }

    fmt.Println("Scanning for dependency files...")
    var sections []ReportSection

    // Find and parse all pom.xml files
    pomFiles, _ := findAllPOMFiles(".")
    if len(pomFiles) > 0 {
        fmt.Printf("Found %d pom.xml file(s).\n", len(pomFiles))
        for _, pf := range pomFiles {
            fmt.Printf(" - %s\n", pf)
        }
        for _, pf := range pomFiles {
            deps, err := parseOneLocalPOMFile(pf)
            if err != nil {
                fmt.Printf("Error parsing %s: %v\n", pf, err)
                continue
            }
            sections = append(sections, ReportSection{
                FilePath:   pf,
                DirectDeps: deps,
                AllDeps:    make(map[string]ExtendedDep),
            })
        }
    }

    // Find and parse all .toml dependency files
    tomlFiles, _ := findAllTOMLFiles(".")
    if len(tomlFiles) > 0 {
        fmt.Printf("Found %d .toml file(s).\n", len(tomlFiles))
        for _, tf := range tomlFiles {
            fmt.Printf(" - %s\n", tf)
        }
        for _, tf := range tomlFiles {
            deps, err := parseTOMLFile(tf)
            if err != nil {
                fmt.Printf("Error parsing %s: %v\n", tf, err)
                continue
            }
            sections = append(sections, ReportSection{
                FilePath:   tf,
                DirectDeps: deps,
                AllDeps:    make(map[string]ExtendedDep),
            })
        }
    }

    // Find and parse all Gradle build files
    gradleFiles, _ := findAllGradleFiles(".")
    if len(gradleFiles) > 0 {
        fmt.Printf("Found %d Gradle build file(s).\n", len(gradleFiles))
        for _, gf := range gradleFiles {
            fmt.Printf(" - %s\n", gf)
        }
        for _, gf := range gradleFiles {
            deps, err := parseBuildGradleFile(gf)
            if err != nil {
                fmt.Printf("Error parsing %s: %v\n", gf, err)
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

    // Close worker channel and wait for all fetches to complete
    channelMutex.Lock()
    channelOpen = false
    channelMutex.Unlock()
    close(pomRequests)
    wgWorkers.Wait()

    // Compute summary counts for each section
    for idx := range sections {
        sec := &sections[idx]
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
        fmt.Printf("Error generating HTML report: %v\n", err)
        os.Exit(1)
    }
    fmt.Println("Analysis complete.")
}

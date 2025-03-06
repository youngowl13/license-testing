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

    // for TOML parsing
    "github.com/pelletier/go-toml"
)

/* ------------------------------------------------------------------------
   1) SHARED CONFIG / CONSTANTS / GLOBALS
------------------------------------------------------------------------ */

const (
    localPOMCacheDir = ".pom-cache"     // local cache for fetched POM files
    pomWorkerCount   = 10               // concurrency worker pool size
    fetchTimeout     = 30 * time.Second // HTTP GET timeout
)

var (
    pomRequests = make(chan fetchRequest, 50)
    wgWorkers   sync.WaitGroup

    pomCache    sync.Map // key = "group:artifact:version" => *MavenPOM
    parentVisit sync.Map // used to detect cycles in parent resolution

    channelOpen  = true
    channelMutex sync.Mutex
)

// Minimal SPDx => (FriendlyName, Copyleft)
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

/* ------------------------------------------------------------------------
   2) COMMON DATA STRUCTURES (POM, BFS, ETC.)
------------------------------------------------------------------------ */

type POMParent struct {
    GroupID    string `xml:"groupId"`
    ArtifactID string `xml:"artifactId"`
    Version    string `xml:"version"`
}

type POMDep struct {
    GroupID    string `xml:"groupId"`
    ArtifactID string `xml:"artifactId"`
    Version    string `xml:"version"`
    Scope      string `xml:"scope"`
    Optional   string `xml:"optional"`
}

// Minimal POM structure
type MavenPOM struct {
    XMLName        xml.Name `xml:"project"`
    GroupID        string   `xml:"groupId"`
    ArtifactID     string   `xml:"artifactId"`
    Version        string   `xml:"version"`
    Parent         POMParent
    Licenses       []struct {
        Name string `xml:"name"`
    } `xml:"licenses>license"`
    Dependencies   []POMDep `xml:"dependencies>dependency"`
    DependencyMgmt struct {
        Dependencies []POMDep `xml:"dependencies>dependency"`
    } `xml:"dependencyManagement"`
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

// BFS concurrency worker
func pomFetchWorker() {
    defer wgWorkers.Done()
    for req := range pomRequests {
        pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
        req.ResultChan <- fetchResult{pom, err}
    }
}

// ----------------------------------------------------------------------
// LICENSE DETECTION & COPYLEFT
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
    // Additional fallback
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
// HELPER: skipScope => ignoring test/provided/system
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
// SHARED: FETCHING & MERGING POMs
// ----------------------------------------------------------------------

func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
    key := fmt.Sprintf("%s:%s:%s", g, a, v)
    if c, ok := pomCache.Load(key); ok {
        return c.(*MavenPOM), nil
    }
    // If not cached, try remote
    pom, err := fetchRemotePOM(g, a, v)
    if err != nil {
        return nil, err
    }
    if pom != nil {
        pomCache.Store(key, pom)
        // fix groupID/version from parent if missing
        if pom.GroupID == "" {
            pom.GroupID = pom.Parent.GroupID
        }
        if pom.Version == "" {
            pom.Version = pom.Parent.Version
        }
        // merge parents
        _ = loadAllParents(pom, 0)
    }
    return pom, err
}

func loadAllParents(p *MavenPOM, depth int) error {
    if p.Parent.GroupID == "" || p.Parent.ArtifactID == "" || p.Parent.Version == "" {
        return nil
    }
    pkey := fmt.Sprintf("%s:%s:%s", p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
    if _, visited := parentVisit.Load(pkey); visited {
        return fmt.Errorf("cycle in parent chain => %s", pkey)
    }
    parentVisit.Store(pkey, true)
    parentPOM, err := retrieveOrLoadPOM(p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
    if err != nil {
        return err
    }
    p.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, p.DependencyMgmt.Dependencies)
    if p.GroupID == "" {
        p.GroupID = parentPOM.GroupID
    }
    if p.Version == "" {
        p.Version = parentPOM.Version
    }
    return loadAllParents(parentPOM, depth+1)
}

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
    for _, val := range outMap {
        merged = append(merged, val)
    }
    sort.Slice(merged, func(i, j int) bool {
        return merged[i].GroupID < merged[j].GroupID
    })
    return merged
}

func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
    groupPath := strings.ReplaceAll(g, ".", "/")
    urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
    urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)

    // Try central first
    if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
        return pm, nil
    }
    // Try google
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
        return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
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

// Provide concurrency-friendly function for BFS calls
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
    key := fmt.Sprintf("%s:%s:%s", g, a, v)
    if c, ok := pomCache.Load(key); ok {
        // cache hit
        return c.(*MavenPOM), nil
    }
    channelMutex.Lock()
    open := channelOpen
    channelMutex.Unlock()
    if !open {
        // channel closed => directly fetch
        pom, err := fetchRemotePOM(g, a, v)
        if err == nil && pom != nil {
            pomCache.Store(key, pom)
        }
        return pom, err
    }
    // else send to channel
    ch := make(chan fetchResult, 1)
    pomRequests <- fetchRequest{GroupID: g, ArtifactID: a, Version: v, ResultChan: ch}
    res := <-ch
    if res.Err == nil && res.POM != nil {
        pomCache.Store(key, res.POM)
    }
    return res.POM, res.Err
}

/* ------------------------------------------------------------------------
   3) HELPER: parseVersionRange, getLatestVersion, etc.
------------------------------------------------------------------------ */

func parseVersionRange(v string) string {
    v = strings.TrimSpace(v)
    // If it's a range like [1.2,2.0)
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

func getLatestVersion(g, a string) (string, error) {
    groupPath := strings.ReplaceAll(g, ".", "/")
    mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
    v, err := fetchLatestVersionFromURL(mavenURL)
    if err == nil && v != "" {
        return v, nil
    }
    googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
    v2, err2 := fetchLatestVersionFromURL(googleURL)
    if err2 == nil && v2 != "" {
        return v2, nil
    }
    return "", fmt.Errorf("no metadata for %s:%s", g, a)
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
        GroupID    string     `xml:"groupId"`
        ArtifactID string     `xml:"artifactId"`
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
    return "", fmt.Errorf("no version found at %s", url)
}

// ----------------------------------------------------------------------
// SPLIT "group/artifact" => (group, artifact)
func splitGA(ga string) (string, string) {
    parts := strings.Split(ga, "/")
    if len(parts) != 2 {
        return "", ""
    }
    return parts[0], parts[1]
}

// parseManagedVersions is used by Gradle BFS to apply <dependencyManagement>
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

/* ------------------------------------------------------------------------
   4) BFS RESULT STRUCTURES
------------------------------------------------------------------------ */

// A standard BFS node
type DependencyNode struct {
    Name       string
    Version    string
    License    string
    Copyleft   bool
    Parent     string
    Transitive []*DependencyNode
}
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

// Flatten for table
type FlatDep struct {
    Name     string
    Version  string
    License  string
    Details  string
    Language string
    Parent   string
    TopLevel string
}

/* ------------------------------------------------------------------------
   5) POM.XML LOGIC
------------------------------------------------------------------------ */

type PomReportSection struct {
    FilePath       string
    DirectDeps     map[string]string // group/artifact => version
    DependencyTree []*DependencyNode
    Flattened      []FlatDep
}

func findAllPOMFiles(root string) ([]string, error) {
    var pomFiles []string
    err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
        if e != nil {
            return e
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

func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
    data, err := os.ReadFile(filePath)
    if err != nil {
        return nil, fmt.Errorf("cannot read local pom.xml '%s': %v", filePath, err)
    }
    var pom MavenPOM
    if e2 := xml.Unmarshal(data, &pom); e2 != nil {
        return nil, fmt.Errorf("error parsing local pom.xml '%s': %v", filePath, e2)
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
        key := g + "/" + a
        depMap[key] = v
    }
    return depMap, nil
}

func buildTransitiveClosureForPOM(sections []PomReportSection) {
    for i := range sections {
        sec := &sections[i]
        visited := make(map[string]bool)
        var roots []*DependencyNode
        var queue []queueItem

        // BFS init from direct
        for ga, ver := range sec.DirectDeps {
            nd := &DependencyNode{
                Name:    ga,
                Version: ver,
                Parent:  "direct",
            }
            roots = append(roots, nd)
            ck := ga + "@" + ver
            visited[ck] = true
            queue = append(queue, queueItem{ga, ver, 1, nd})
        }
        for len(queue) > 0 {
            it := queue[0]
            queue = queue[1:]
            g, a := splitGA(it.GroupArtifact)
            if g == "" || a == "" {
                continue
            }
            if strings.ToLower(it.Version) == "unknown" {
                continue
            }
            pom, err := concurrentFetchPOM(g, a, it.Version)
            if err != nil || pom == nil {
                continue
            }
            if it.ParentNode != nil {
                lic := detectLicense(pom)
                it.ParentNode.License = lic
                it.ParentNode.Copyleft = isCopyleft(lic)
            }
            for _, d := range pom.Dependencies {
                if skipScope(d.Scope, d.Optional) {
                    continue
                }
                childGA := d.GroupID + "/" + d.ArtifactID
                cv := d.Version
                if cv == "" {
                    cv = "unknown"
                }
                ckey := childGA + "@" + cv
                if visited[ckey] {
                    continue
                }
                visited[ckey] = true
                childNode := &DependencyNode{
                    Name:    childGA,
                    Version: cv,
                    Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
                }
                it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
                queue = append(queue, queueItem{childGA, cv, it.Depth + 1, childNode})
            }
        }
        // Flatten
        var flat []FlatDep
        for _, root := range roots {
            flattenDependencyNode(root, "POM-TOP", &flat)
        }
        // Sort
        sort.SliceStable(flat, func(i, j int) bool {
            gi := getLicenseGroup(flat[i].License)
            gj := getLicenseGroup(flat[j].License)
            return gi < gj
        })
        sec.DependencyTree = roots
        sec.Flattened = flat
    }
}

/* ------------------------------------------------------------------------
   6) TOML LOGIC
------------------------------------------------------------------------ */

type TomlReportSection struct {
    FilePath       string
    DirectDeps     map[string]string
    DependencyTree []*DependencyNode
    Flattened      []FlatDep
}

func findTOMLFile(root string) ([]string, error) {
    var result []string
    err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
        if e != nil {
            return e
        }
        if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
            result = append(result, path)
        }
        return nil
    })
    return result, err
}

func parseTOMLFile(filePath string) (map[string]string, error) {
    tree, err := toml.LoadFile(filePath)
    if err != nil {
        return nil, fmt.Errorf("toml load error: %v", err)
    }
    versions, err := loadTomlVersions(tree)
    if err != nil {
        return nil, err
    }
    librariesTree := tree.Get("libraries")
    if librariesTree == nil {
        return nil, fmt.Errorf("no 'libraries' table in %s", filePath)
    }
    libs, ok := librariesTree.(*toml.Tree)
    if !ok {
        return nil, fmt.Errorf("'libraries' not a valid TOML table in %s", filePath)
    }
    deps := make(map[string]string)
    for _, libKey := range libs.Keys() {
        libVal := libs.Get(libKey)
        if libVal == nil {
            continue
        }
        lib, ok2 := libVal.(*toml.Tree)
        if !ok2 {
            continue
        }
        moduleStr, _ := lib.Get("module").(string)
        versionRef, _ := lib.Get("version.ref").(string)
        if moduleStr == "" || versionRef == "" {
            continue
        }
        versionVal, ok3 := versions[versionRef]
        if !ok3 {
            versionVal = "unknown"
        }
        parts := strings.Split(moduleStr, ":")
        if len(parts) != 2 {
            continue
        }
        group := parts[0]
        artif := parts[1]
        key := group + "/" + artif
        deps[key] = versionVal
    }
    return deps, nil
}

func loadTomlVersions(tree *toml.Tree) (map[string]string, error) {
    res := make(map[string]string)
    verObj := tree.Get("versions")
    if verObj == nil {
        return res, nil
    }
    verTree, ok := verObj.(*toml.Tree)
    if !ok {
        return nil, fmt.Errorf("'versions' not a valid TOML table")
    }
    for _, k := range verTree.Keys() {
        val := verTree.Get(k)
        switch v := val.(type) {
        case string:
            res[k] = v
        }
    }
    return res, nil
}

func buildTransitiveClosureForToml(tsecs []TomlReportSection) {
    for i := range tsecs {
        sec := &tsecs[i]
        visited := make(map[string]bool)
        var roots []*DependencyNode
        var queue []queueItem

        // BFS init
        for ga, ver := range sec.DirectDeps {
            nd := &DependencyNode{
                Name:    ga,
                Version: ver,
                Parent:  "direct",
            }
            roots = append(roots, nd)
            ck := ga + "@" + ver
            visited[ck] = true
            queue = append(queue, queueItem{ga, ver, 1, nd})
        }

        for len(queue) > 0 {
            it := queue[0]
            queue = queue[1:]
            g, a := splitGA(it.GroupArtifact)
            if g == "" || a == "" {
                continue
            }
            if strings.ToLower(it.Version) == "unknown" {
                continue
            }
            pom, err := concurrentFetchPOM(g, a, it.Version)
            if err != nil || pom == nil {
                continue
            }
            if it.ParentNode != nil {
                lic := detectLicense(pom)
                it.ParentNode.License = lic
                it.ParentNode.Copyleft = isCopyleft(lic)
            }
            for _, d := range pom.Dependencies {
                if skipScope(d.Scope, d.Optional) {
                    continue
                }
                childGA := d.GroupID + "/" + d.ArtifactID
                cv := d.Version
                if cv == "" {
                    cv = "unknown"
                }
                ckey := childGA + "@" + cv
                if visited[ckey] {
                    continue
                }
                visited[ckey] = true
                childNode := &DependencyNode{
                    Name:    childGA,
                    Version: cv,
                    Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
                }
                it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
                queue = append(queue, queueItem{childGA, cv, it.Depth + 1, childNode})
            }
        }
        var flat []FlatDep
        for _, root := range roots {
            flattenDependencyNode(root, "TOML-TOP", &flat)
        }
        sort.SliceStable(flat, func(i, j int) bool {
            gi := getLicenseGroup(flat[i].License)
            gj := getLicenseGroup(flat[j].License)
            return gi < gj
        })
        sec.DependencyTree = roots
        sec.Flattened = flat
    }
}

/* ------------------------------------------------------------------------
   7) GRADLE LOGIC
------------------------------------------------------------------------ */

type GradleReportSection struct {
    FilePath       string
    Dependencies   map[string]ExtendedDepInfo
    DependencyTree []*GradleDependencyNode
    Flattened      []FlatDep
}

type GradleDependencyNode struct {
    Name       string
    Version    string
    License    string
    Copyleft   bool
    Parent     string
    Transitive []*GradleDependencyNode
}

type ExtendedDepInfo struct {
    Display string
    Lookup  string
    Parent  string
}

// find build.gradle
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

func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
    data, err := os.ReadFile(filePath)
    if err != nil {
        return nil, err
    }
    content := string(data)
    varMap := parseGradleVariables(content)

    deps := make(map[string]ExtendedDepInfo)
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
        ga := group + "/" + artifact
        key := ga + "@" + version
        deps[key] = ExtendedDepInfo{
            Display: version,
            Lookup:  version,
            Parent:  "direct",
        }
    }
    return deps, nil
}

// parseGradleVariables => parse `def varName = "1.2.3"`
func parseGradleVariables(content string) map[string]string {
    varMap := make(map[string]string)
    re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
    matches := re.FindAllStringSubmatch(content, -1)
    for _, match := range matches {
        varMap[match[1]] = match[2]
    }
    return varMap
}

func buildTransitiveClosureForGradle(gsecs []GradleReportSection) {
    for i := range gsecs {
        sec := &gsecs[i]
        visited := make(map[string]bool)
        nodeMap := make(map[string]*GradleDependencyNode)
        var roots []*GradleDependencyNode
        var queue []queueItem

        // BFS init
        for depKey, info := range sec.Dependencies {
            visited[depKey] = true
            n := &GradleDependencyNode{
                Name:   strings.Split(depKey, "@")[0],
                Version: info.Lookup,
                Parent: "direct",
            }
            roots = append(roots, n)
            nodeMap[depKey] = n
            queue = append(queue, queueItem{
                GroupArtifact: strings.Split(depKey, "@")[0],
                Version:       info.Lookup,
                Depth:         1,
                ParentNode:    nil,
            })
        }

        // BFS
        for len(queue) > 0 {
            it := queue[0]
            queue = queue[1:]
            gid, aid := splitGA(it.GroupArtifact)
            if gid == "" || aid == "" {
                continue
            }
            // fallback to latest if unknown
            ver := it.Version
            if strings.Contains(ver, "${") || strings.ToLower(ver) == "unknown" {
                latest, err := getLatestVersion(gid, aid)
                if err != nil {
                    ver = "unknown"
                } else {
                    ver = latest
                }
            }
            pom, err := concurrentFetchPOM(gid, aid, ver)
            if err != nil || pom == nil {
                continue
            }
            depKey := fmt.Sprintf("%s@%s", it.GroupArtifact, ver)
            currentNode, ok := nodeMap[depKey]
            if !ok {
                currentNode = &GradleDependencyNode{
                    Name:    it.GroupArtifact,
                    Version: ver,
                    Parent:  "???",
                }
                nodeMap[depKey] = currentNode
            }
            // License
            lic := detectLicense(pom)
            currentNode.License = lic
            currentNode.Copyleft = isCopyleft(lic)

            // sub-deps
            managed := parseManagedVersions(pom)
            for _, d := range pom.Dependencies {
                if skipScope(d.Scope, d.Optional) {
                    continue
                }
                childGA := d.GroupID + "/" + d.ArtifactID
                cv := parseVersionRange(d.Version)
                if cv == "" || strings.Contains(cv, "${") {
                    if mv, ok2 := managed[childGA]; ok2 && mv != "" {
                        cv = mv
                    } else {
                        latest, e2 := getLatestVersion(d.GroupID, d.ArtifactID)
                        if e2 != nil {
                            cv = "unknown"
                        } else {
                            cv = latest
                        }
                    }
                }
                if cv == "" {
                    cv = "unknown"
                }
                ckey := childGA + "@" + cv
                if visited[ckey] {
                    continue
                }
                visited[ckey] = true
                childNode := &GradleDependencyNode{
                    Name:    childGA,
                    Version: cv,
                    Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, ver),
                }
                currentNode.Transitive = append(currentNode.Transitive, childNode)
                queue = append(queue, queueItem{childGA, cv, it.Depth + 1, nil})
                nodeMap[ckey] = childNode
            }
        }

        // flatten BFS
        var flat []FlatDep
        for _, root := range roots {
            flattenGradleNode(root, "GRADLE-TOP", &flat)
        }
        // sort
        sort.SliceStable(flat, func(i, j int) bool {
            gi := getLicenseGroup(flat[i].License)
            gj := getLicenseGroup(flat[j].License)
            return gi < gj
        })
        sec.DependencyTree = roots
        sec.Flattened = flat
    }
}

/* ------------------------------------------------------------------------
   8) FLATTEN NODES
------------------------------------------------------------------------ */

func flattenDependencyNode(nd *DependencyNode, top string, out *[]FlatDep) {
    details := fmt.Sprintf("https://repo1.maven.org/maven2/%s", nd.Name)
    fd := FlatDep{
        Name:     nd.Name,
        Version:  nd.Version,
        License:  nd.License,
        Details:  details,
        Language: "maven",
        Parent:   nd.Parent,
        TopLevel: top,
    }
    *out = append(*out, fd)
    for _, sub := range nd.Transitive {
        flattenDependencyNode(sub, top, out)
    }
}

func flattenGradleNode(nd *GradleDependencyNode, top string, out *[]FlatDep) {
    details := fmt.Sprintf("https://repo1.maven.org/maven2/%s", nd.Name)
    fd := FlatDep{
        Name:     nd.Name,
        Version:  nd.Version,
        License:  nd.License,
        Details:  details,
        Language: "gradle",
        Parent:   nd.Parent,
        TopLevel: top,
    }
    *out = append(*out, fd)
    for _, sub := range nd.Transitive {
        flattenGradleNode(sub, top, out)
    }
}

// getLicenseGroup => 1 => copyleft, 2 => unknown, 3 => everything else
func getLicenseGroup(license string) int {
    if isCopyleft(license) {
        return 1
    } else if license == "Unknown" {
        return 2
    }
    return 3
}

/* ------------------------------------------------------------------------
   9) FINAL HTML REPORT
------------------------------------------------------------------------ */

var finalReportTemplate = `
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Maven Multi-File Dependency License Report</title>
<style>
body{font-family:Arial,sans-serif;margin:20px}
h1,h2{color:#2c3e50}
table{width:100%;border-collapse:collapse;margin-bottom:20px}
th,td{border:1px solid #ddd;padding:8px;text-align:left}
th{background:#f2f2f2}
.copyleft{background:#f8d7da;color:#721c24}
.non-copyleft{background:#d4edda;color:#155724}
.unknown{background:#ffff99;color:#333}
details{margin:4px 0}
summary{cursor:pointer;font-weight:bold}
</style>
</head>
<body>
<h1>Maven Multi-File Dependency License Report</h1>

{{range .PomSections}}
<h2>POM Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No POM dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Details</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.Details}}" target="_blank">{{.Details}}</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.TreeHTML}}
</div>
<hr/>
{{end}}

{{range .TomlSections}}
<h2>TOML Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No TOML dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Details</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.Details}}" target="_blank">{{.Details}}</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.TreeHTML}}
</div>
<hr/>
{{end}}

{{range .GradleSections}}
<h2>Gradle Dependencies (from: {{.FilePath}})</h2>
{{if eq (len .Flattened) 0}}
<p>No Gradle dependencies found.</p>
{{else}}
<table>
<tr>
  <th>Name</th>
  <th>Version</th>
  <th>License</th>
  <th>Parent</th>
  <th>Top-Level</th>
  <th>Language</th>
  <th>Details</th>
</tr>
{{range .Flattened}}
<tr>
  <td>{{.Name}}</td>
  <td>{{.Version}}</td>
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.Details}}" target="_blank">{{.Details}}</a></td>
</tr>
{{end}}
</table>
{{end}}
<h3>BFS Expansions</h3>
<div>
{{.TreeHTML}}
</div>
<hr/>
{{end}}

</body>
</html>
`

// BFS expansions for POM + TOML (DependencyNode)
func buildPomTreeHTML(node *DependencyNode) string {
    sum := fmt.Sprintf("%s@%s (License: %s)", node.Name, node.Version, node.License)
    cls := "non-copyleft"
    if node.License == "Unknown" {
        cls = "unknown"
    } else if isCopyleft(node.License) {
        cls = "copyleft"
    }
    var sb strings.Builder
    sb.WriteString("<details><summary class=\"" + cls + "\">")
    sb.WriteString(template.HTMLEscapeString(sum))
    sb.WriteString("</summary>\n")
    if len(node.Transitive) > 0 {
        sb.WriteString("<ul>\n")
        for _, ch := range node.Transitive {
            sb.WriteString("<li>")
            sb.WriteString(buildPomTreeHTML(ch))
            sb.WriteString("</li>\n")
        }
        sb.WriteString("</ul>\n")
    }
    sb.WriteString("</details>\n")
    return sb.String()
}
func buildPomTreesHTML(nodes []*DependencyNode) string {
    if len(nodes) == 0 {
        return "<p>No BFS expansions found.</p>"
    }
    var sb strings.Builder
    for _, n := range nodes {
        sb.WriteString(buildPomTreeHTML(n))
    }
    return sb.String()
}

// BFS expansions for GradleDependencyNode
func buildGradleTreeHTML(nd *GradleDependencyNode) string {
    sum := fmt.Sprintf("%s@%s (License: %s)", nd.Name, nd.Version, nd.License)
    cls := "non-copyleft"
    if nd.License == "Unknown" {
        cls = "unknown"
    } else if isCopyleft(nd.License) {
        cls = "copyleft"
    }
    var sb strings.Builder
    sb.WriteString("<details><summary class=\"" + cls + "\">")
    sb.WriteString(template.HTMLEscapeString(sum))
    sb.WriteString("</summary>\n")
    if len(nd.Transitive) > 0 {
        sb.WriteString("<ul>\n")
        for _, ch := range nd.Transitive {
            sb.WriteString("<li>")
            sb.WriteString(buildGradleTreeHTML(ch))
            sb.WriteString("</li>\n")
        }
        sb.WriteString("</ul>\n")
    }
    sb.WriteString("</details>\n")
    return sb.String()
}
func buildGradleTreesHTML(nodes []*GradleDependencyNode) string {
    if len(nodes) == 0 {
        return "<p>No BFS expansions found.</p>"
    }
    var sb strings.Builder
    for _, n := range nodes {
        sb.WriteString(buildGradleTreeHTML(n))
    }
    return sb.String()
}

/* ------------------------------------------------------------------------
   10) MAIN
------------------------------------------------------------------------ */

func main() {
    // Start concurrency worker pool
    for i := 0; i < pomWorkerCount; i++ {
        wgWorkers.Add(1)
        go pomFetchWorker()
    }

    // 1) Process POM files
    pomFiles, _ := findAllPOMFiles(".")
    var pomSections []PomReportSection
    for _, pf := range pomFiles {
        direct, err := parseOneLocalPOMFile(pf)
        if err != nil {
            fmt.Printf("Error parsing POM %s => %v\n", pf, err)
            continue
        }
        pomSections = append(pomSections, PomReportSection{
            FilePath:   pf,
            DirectDeps: direct,
        })
    }
    buildTransitiveClosureForPOM(pomSections)

    // 2) Process TOML files
    tomlFiles, _ := findTOMLFile(".")
    var tomlSections []TomlReportSection
    for _, tf := range tomlFiles {
        deps, err := parseTOMLFile(tf)
        if err != nil {
            fmt.Printf("Error parsing TOML %s => %v\n", tf, err)
            continue
        }
        tomlSections = append(tomlSections, TomlReportSection{
            FilePath:   tf,
            DirectDeps: deps,
        })
    }
    buildTransitiveClosureForToml(tomlSections)

    // 3) Process Gradle files
    gradleFiles, _ := findBuildGradleFiles(".")
    var gradleSections []GradleReportSection
    for _, gf := range gradleFiles {
        direct, err := parseBuildGradleFile(gf)
        if err != nil {
            fmt.Printf("Error parsing Gradle %s => %v\n", gf, err)
            continue
        }
        gradleSections = append(gradleSections, GradleReportSection{
            FilePath:     gf,
            Dependencies: direct,
        })
    }
    buildTransitiveClosureForGradle(gradleSections)

    // Close the channel, wait for worker pool
    channelMutex.Lock()
    channelOpen = false
    channelMutex.Unlock()
    close(pomRequests)
    wgWorkers.Wait()

    // Prepare BFS expansions for each section
    //  (like Node/Python code that built "HTML expansions")
    type pomHTMLSection struct {
        FilePath  string
        Flattened []FlatDep
        TreeHTML  template.HTML
    }
    var finalPom []pomHTMLSection
    for _, ps := range pomSections {
        var sb strings.Builder
        sb.WriteString(buildPomTreesHTML(ps.DependencyTree))
        finalPom = append(finalPom, pomHTMLSection{
            FilePath:  ps.FilePath,
            Flattened: ps.Flattened,
            TreeHTML:  template.HTML(sb.String()),
        })
    }

    type tomlHTMLSection struct {
        FilePath  string
        Flattened []FlatDep
        TreeHTML  template.HTML
    }
    var finalToml []tomlHTMLSection
    for _, ts := range tomlSections {
        var sb strings.Builder
        sb.WriteString(buildPomTreesHTML(ts.DependencyTree))
        finalToml = append(finalToml, tomlHTMLSection{
            FilePath:  ts.FilePath,
            Flattened: ts.Flattened,
            TreeHTML:  template.HTML(sb.String()),
        })
    }

    type gradleHTMLSection struct {
        FilePath  string
        Flattened []FlatDep
        TreeHTML  template.HTML
    }
    var finalGradle []gradleHTMLSection
    for _, gs := range gradleSections {
        var sb strings.Builder
        sb.WriteString(buildGradleTreesHTML(gs.DependencyTree))
        finalGradle = append(finalGradle, gradleHTMLSection{
            FilePath:  gs.FilePath,
            Flattened: gs.Flattened,
            TreeHTML:  template.HTML(sb.String()),
        })
    }

    // Combine them for one final template
    data := struct {
        PomSections    []pomHTMLSection
        TomlSections   []tomlHTMLSection
        GradleSections []gradleHTMLSection
    }{
        finalPom,
        finalToml,
        finalGradle,
    }

    tmpl, err := template.New("report").Funcs(template.FuncMap{
        "isCopyleft": isCopyleft,
    }).Parse(finalReportTemplate)
    if err != nil {
        fmt.Printf("Template parse error: %v\n", err)
        return
    }

    outFile, err := os.Create("maven-multi-file-report.html")
    if err != nil {
        fmt.Printf("Cannot create output file: %v\n", err)
        return
    }
    defer outFile.Close()

    if err := tmpl.Execute(outFile, data); err != nil {
        fmt.Printf("Template exec error: %v\n", err)
        return
    }

    fmt.Println("maven-multi-file-report.html generated successfully!")
}

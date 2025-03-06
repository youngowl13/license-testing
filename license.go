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
	pomWorkerCount = 10           // concurrency worker count
	fetchTimeout   = 30 * time.Second
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map
	parentVisit  sync.Map

	channelOpen  = true
	channelMutex sync.Mutex
)

// SPDx minimal + copyleft detection
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

// getLicenseGroup => for sorting: copyleft=1, unknown=2, others=3
func getLicenseGroup(license string) int {
	if isCopyleft(license) {
		return 1
	} else if strings.EqualFold(license, "unknown") {
		return 2
	}
	return 3
}

func isCopyleft(license string) bool {
	// 1) Check SPDx
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(license, data.Name) ||
			strings.EqualFold(license, spdxID)) {
			return true
		}
	}
	// 2) fallback keywords
	keywords := []string{
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
	up := strings.ToUpper(license)
	for _, k := range keywords {
		if strings.Contains(up, strings.ToUpper(k)) {
			return true
		}
	}
	return false
}

// ----------------------------------------------------------------------
// 2) BFS concurrency: fetchRequest => fetchRemotePOM => concurrency
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
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
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
	req := fetchRequest{GroupID: g, ArtifactID: a, Version: v, ResultChan: make(chan fetchResult, 1)}
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// fallbackVersionIfUnknown => if version="unknown" => tries getLatestVersion
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

// getLatestVersion => tries central, google
func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	u1 := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, e := fetchLatestVersionFromURL(u1); e == nil && v != "" {
		return v, nil
	}
	u2 := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v2, e2 := fetchLatestVersionFromURL(u2); e2 == nil && v2 != "" {
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
	return "", fmt.Errorf("no version found in %s", url)
}

// ----------------------------------------------------------------------
// 3) MAVEN POM data structure + BFS
// ----------------------------------------------------------------------

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
type MavenPOM struct {
	XMLName xml.Name `xml:"project"`

	GroupID     string
	ArtifactID  string
	Version     string
	Parent      POMParent
	Licenses    []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
}

// fetchRemotePOM => tries central, google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)

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

// skip test/provided/system/optional
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

// merges <dependencyManagement> from parents
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
	for _, v := range outMap {
		merged = append(merged, v)
	}
	sort.Slice(merged, func(i, j int) bool {
		return merged[i].GroupID < merged[j].GroupID
	})
	return merged
}

// BFS to load all parents
func loadAllParents(p *MavenPOM, depth int) error {
	if p.Parent.GroupID == "" || p.Parent.ArtifactID == "" || p.Parent.Version == "" {
		return nil
	}
	pkey := fmt.Sprintf("%s:%s:%s", p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if _, visited := parentVisit.Load(pkey); visited {
		return fmt.Errorf("cycle in parent chain => %s", pkey)
	}
	parentVisit.Store(pkey, true)
	ppom, err := retrieveOrLoadPOM(p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if err != nil {
		return err
	}
	p.DependencyMgmt.Dependencies = mergeDepMgmt(ppom.DependencyMgmt.Dependencies, p.DependencyMgmt.Dependencies)
	if p.GroupID == "" {
		p.GroupID = ppom.GroupID
	}
	if p.Version == "" {
		p.Version = ppom.Version
	}
	return loadAllParents(ppom, depth+1)
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
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || up == strings.ToUpper(spdxID) {
			return data.Name
		}
	}
	return lic
}

// ----------------------------------------------------------------------
// 4) FILE SEARCH + PARSING: pom.xml => findAllPOMFiles, parseOneLocalPOMFile
//                           .toml   => findTOMLFile, parseTOMLFile
//                           build.gradle => findBuildGradleFiles, parseBuildGradleFile
// ----------------------------------------------------------------------

func findAllPOMFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}
func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read local pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if e2 := xml.Unmarshal(dat, &pom); e2 != nil {
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

func findTOMLFile(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".toml") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}
func parseTOMLFile(filePath string) (map[string]string, error) {
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("error parsing TOML '%s': %v", filePath, err)
	}
	vers, err := loadTomlVersions(tree)
	if err != nil {
		return nil, err
	}
	lib := tree.Get("libraries")
	if lib == nil {
		return nil, fmt.Errorf("no 'libraries' table in %s", filePath)
	}
	libraries, ok := lib.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' not a valid TOML table in %s", filePath)
	}
	deps := make(map[string]string)
	for _, k := range libraries.Keys() {
		val := libraries.Get(k)
		if val == nil {
			continue
		}
		sub, ok2 := val.(*toml.Tree)
		if !ok2 {
			continue
		}
		moduleStr, _ := sub.Get("module").(string)
		versionRef, _ := sub.Get("version.ref").(string)
		if moduleStr == "" || versionRef == "" {
			continue
		}
		actualVer, found := vers[versionRef]
		if !found {
			actualVer = "unknown"
		}
		parts := strings.SplitN(moduleStr, ":", 2)
		if len(parts) != 2 {
			continue
		}
		g := parts[0]
		a := parts[1]
		key := g + "/" + a
		deps[key] = actualVer
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
		return nil, fmt.Errorf("'versions' is not a valid table")
	}
	for _, k := range verTree.Keys() {
		val := verTree.Get(k)
		if s, ok2 := val.(string); ok2 {
			res[k] = s
		}
	}
	return res, nil
}

func findBuildGradleFiles(root string) ([]string, error) {
	var out []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			out = append(out, path)
		}
		return nil
	})
	return out, err
}

// ExtendedDepInfo => for gradle direct BFS
type ExtendedDepInfo struct {
	Display string
	Lookup  string
	Parent  string
}
func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read build.gradle '%s': %v", filePath, err)
	}
	content := string(dat)
	varMap := parseGradleVariables(content)

	deps := make(map[string]ExtendedDepInfo)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		depStr := m[2]
		p := strings.Split(depStr, ":")
		if len(p) < 2 {
			continue
		}
		group := p[0]
		artifact := p[1]
		version := "unknown"
		if len(p) >= 3 {
			version = parseVersionRange(p[2])
			if strings.Contains(version, "${") {
				varRe := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = varRe.ReplaceAllStringFunc(version, func(s string) string {
					inner := s[2 : len(s)-1]
					if v2, ok := varMap[inner]; ok {
						return v2
					}
					return ""
				})
				if version == "" {
					version = "unknown"
				}
			}
		}
		key := group + "/" + artifact + "@" + version
		deps[key] = ExtendedDepInfo{
			Display: version,
			Lookup:  version,
			Parent:  "direct",
		}
	}
	return deps, nil
}
func parseGradleVariables(content string) map[string]string {
	varMap := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		varMap[match[1]] = match[2]
	}
	return varMap
}

// ----------------------------------------------------------------------
// 5) BFS NODES + Flatten + BFS expansions
// ----------------------------------------------------------------------

type DependencyNode struct {
	Name            string
	OriginalVersion string
	EffectiveVer    string
	License         string
	Copyleft        bool
	Parent          string
	TopLevel        string
	Transitive      []*DependencyNode
}

type GradleDependencyNode struct {
	Name            string
	OriginalVersion string
	EffectiveVer    string
	License         string
	Copyleft        bool
	Parent          string
	TopLevel        string
	Transitive      []*GradleDependencyNode
}

// single link column
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Language string
	Parent   string
	TopLevel string

	RepoInfoURL string
}

// BFS expansions
func buildPOMTreeHTML(n *DependencyNode) string {
	sum := fmt.Sprintf("%s@%s (License: %s)", n.Name, n.EffectiveVer, n.License)
	if n.OriginalVersion != n.EffectiveVer && strings.ToLower(n.OriginalVersion) == "unknown" {
		sum += " [source missing => used " + n.EffectiveVer + "]"
	}
	cls := "non-copyleft"
	if n.License == "Unknown" {
		cls = "unknown"
	} else if isCopyleft(n.License) {
		cls = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details><summary class=\"" + cls + "\">")
	sb.WriteString(template.HTMLEscapeString(sum))
	sb.WriteString("</summary>\n")
	if len(n.Transitive) > 0 {
		sb.WriteString("<ul>\n")
		for _, c := range n.Transitive {
			sb.WriteString("<li>")
			sb.WriteString(buildPOMTreeHTML(c))
			sb.WriteString("</li>\n")
		}
		sb.WriteString("</ul>\n")
	}
	sb.WriteString("</details>\n")
	return sb.String()
}
func buildPOMTreesHTML(nodes []*DependencyNode) string {
	if len(nodes) == 0 {
		return "<p>No BFS expansions found.</p>"
	}
	var sb strings.Builder
	for _, n := range nodes {
		sb.WriteString(buildPOMTreeHTML(n))
	}
	return sb.String()
}

func buildGradleTreeHTML(n *GradleDependencyNode) string {
	sum := fmt.Sprintf("%s@%s (License: %s)", n.Name, n.EffectiveVer, n.License)
	if n.OriginalVersion != n.EffectiveVer && strings.ToLower(n.OriginalVersion) == "unknown" {
		sum += " [source missing => used " + n.EffectiveVer + "]"
	}
	cls := "non-copyleft"
	if n.License == "Unknown" {
		cls = "unknown"
	} else if isCopyleft(n.License) {
		cls = "copyleft"
	}
	var sb strings.Builder
	sb.WriteString("<details><summary class=\"" + cls + "\">")
	sb.WriteString(template.HTMLEscapeString(sum))
	sb.WriteString("</summary>\n")
	if len(n.Transitive) > 0 {
		sb.WriteString("<ul>\n")
		for _, c := range n.Transitive {
			sb.WriteString("<li>")
			sb.WriteString(buildGradleTreeHTML(c))
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

// buildRepoInfoLink => always google maven if parseable, else google search
func buildRepoInfoLink(g, a, v string) string {
	if g == "" || a == "" {
		q := g + " " + a + " " + v
		return "https://www.google.com/search?q=" + strings.ReplaceAll(q, " ", "+")
	}
	return fmt.Sprintf("https://maven.google.com/web/index.html?q=%s#%s:%s:%s", a, g, a, v)
}

// Flatten for POM BFS
func flattenPOMNode(n *DependencyNode, out *[]FlatDep) {
	g, a := splitGA(n.Name)
	ver := n.OriginalVersion
	if strings.ToLower(ver) == "unknown" && n.EffectiveVer != "unknown" {
		ver = "missing in source => " + n.EffectiveVer
	}
	repoLink := buildRepoInfoLink(g, a, n.EffectiveVer)
	fd := FlatDep{
		Name:       n.Name,
		Version:    ver,
		License:    n.License,
		Language:   "maven",
		Parent:     n.Parent,
		TopLevel:   n.TopLevel,
		RepoInfoURL: repoLink,
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenPOMNode(c, out)
	}
}

// Flatten for Gradle BFS
func flattenGradleNode(n *GradleDependencyNode, out *[]FlatDep) {
	g, a := splitGA(n.Name)
	ver := n.OriginalVersion
	if strings.ToLower(ver) == "unknown" && n.EffectiveVer != "unknown" {
		ver = "missing in source => " + n.EffectiveVer
	}
	repoLink := buildRepoInfoLink(g, a, n.EffectiveVer)
	fd := FlatDep{
		Name:       n.Name,
		Version:    ver,
		License:    n.License,
		Language:   "gradle",
		Parent:     n.Parent,
		TopLevel:   n.TopLevel,
		RepoInfoURL: repoLink,
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenGradleNode(c, out)
	}
}

// ----------------------------------------------------------------------
// 8) BFS STRUCTS => POM approach, TOML approach, Gradle approach
// ----------------------------------------------------------------------

type PomReportSection struct {
	FilePath       string
	DirectDeps     map[string]string
	DependencyTree []*DependencyNode
	Flattened      []FlatDep
}
type TomlReportSection struct {
	FilePath       string
	DirectDeps     map[string]string
	DependencyTree []*DependencyNode
	Flattened      []FlatDep
}
type GradleReportSection struct {
	FilePath       string
	Dependencies   map[string]ExtendedDepInfo
	DependencyTree []*GradleDependencyNode
	Flattened      []FlatDep
}

// BFS for POM
func buildTransitiveClosureForPOM(secs []PomReportSection) {
	for i := range secs {
		sec := &secs[i]
		visited := make(map[string]bool)
		var roots []*DependencyNode
		var queue []struct {
			ga string
			ov string
			dn *DependencyNode
		}
		for ga, ver := range sec.DirectDeps {
			n := &DependencyNode{
				Name:            ga,
				OriginalVersion: ver,
				EffectiveVer:    ver,
				Parent:          "direct",
				TopLevel:        ga,
			}
			roots = append(roots, n)
			visited[ga+"@"+ver] = true
			queue = append(queue, struct {
				ga string
				ov string
				dn *DependencyNode
			}{ga, ver, n})
		}
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			g, a := splitGA(it.ga)
			if g == "" || a == "" {
				continue
			}
			eff, e2 := fallbackVersionIfUnknown(g, a, it.ov)
			it.dn.EffectiveVer = eff
			if e2 != nil {
				continue
			}
			if strings.ToLower(eff) == "unknown" {
				continue
			}
			pom, err := concurrentFetchPOM(g, a, eff)
			if err != nil || pom == nil {
				continue
			}
			lic := detectLicense(pom)
			it.dn.License = lic
			it.dn.Copyleft = isCopyleft(lic)

			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				cga := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				key := cga + "@" + cv
				if visited[key] {
					continue
				}
				visited[key] = true
				child := &DependencyNode{
					Name:            cga,
					OriginalVersion: cv,
					EffectiveVer:    cv,
					Parent:          it.ga + ":" + eff,
					TopLevel:        it.dn.TopLevel,
				}
				it.dn.Transitive = append(it.dn.Transitive, child)
				queue = append(queue, struct {
					ga string
					ov string
					dn *DependencyNode
				}{cga, cv, child})
			}
		}
		// Flatten
		var flat []FlatDep
		for _, r := range roots {
			flattenPOMNode(r, &flat)
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

// BFS for TOML
func buildTransitiveClosureForToml(tsecs []TomlReportSection) {
	for i := range tsecs {
		sec := &tsecs[i]
		visited := make(map[string]bool)
		var roots []*DependencyNode
		var queue []struct {
			ga string
			ov string
			dn *DependencyNode
		}
		for ga, ver := range sec.DirectDeps {
			n := &DependencyNode{
				Name:            ga,
				OriginalVersion: ver,
				EffectiveVer:    ver,
				Parent:          "direct",
				TopLevel:        ga,
			}
			roots = append(roots, n)
			visited[ga+"@"+ver] = true
			queue = append(queue, struct {
				ga string
				ov string
				dn *DependencyNode
			}{ga, ver, n})
		}
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			g, a := splitGA(it.ga)
			if g == "" || a == "" {
				continue
			}
			eff, e2 := fallbackVersionIfUnknown(g, a, it.ov)
			it.dn.EffectiveVer = eff
			if e2 != nil {
				continue
			}
			if strings.ToLower(eff) == "unknown" {
				continue
			}
			pom, err := concurrentFetchPOM(g, a, eff)
			if err != nil || pom == nil {
				continue
			}
			lic := detectLicense(pom)
			it.dn.License = lic
			it.dn.Copyleft = isCopyleft(lic)

			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				cga := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				key := cga + "@" + cv
				if visited[key] {
					continue
				}
				visited[key] = true
				child := &DependencyNode{
					Name:            cga,
					OriginalVersion: cv,
					EffectiveVer:    cv,
					Parent:          it.ga + ":" + eff,
					TopLevel:        it.dn.TopLevel,
				}
				it.dn.Transitive = append(it.dn.Transitive, child)
				queue = append(queue, struct {
					ga string
					ov string
					dn *DependencyNode
				}{cga, cv, child})
			}
		}
		var flat []FlatDep
		for _, root := range roots {
			flattenPOMNode(root, &flat)
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

// BFS for Gradle
func buildTransitiveClosureForGradle(gsecs []GradleReportSection) {
	for i := range gsecs {
		sec := &gsecs[i]
		visited := make(map[string]bool)
		var roots []*GradleDependencyNode
		var queue []struct {
			ga string
			ov string
			dn *GradleDependencyNode
		}
		for depKey, info := range sec.Dependencies {
			p := strings.SplitN(depKey, "@", 2)
			if len(p) != 2 {
				continue
			}
			ga := p[0]
			ov := info.Lookup
			visited[depKey] = true
			n := &GradleDependencyNode{
				Name:            ga,
				OriginalVersion: ov,
				EffectiveVer:    ov,
				Parent:          "direct",
				TopLevel:        ga,
			}
			roots = append(roots, n)
			queue = append(queue, struct {
				ga string
				ov string
				dn *GradleDependencyNode
			}{ga, ov, n})
		}
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			g, a := splitGA(it.ga)
			if g == "" || a == "" {
				continue
			}
			eff, e2 := fallbackVersionIfUnknown(g, a, it.ov)
			it.dn.EffectiveVer = eff
			if e2 != nil {
				continue
			}
			if strings.ToLower(eff) == "unknown" {
				continue
			}
			pom, err := concurrentFetchPOM(g, a, eff)
			if err != nil || pom == nil {
				continue
			}
			lic := detectLicense(pom)
			it.dn.License = lic
			it.dn.Copyleft = isCopyleft(lic)

			// parse depMgmt
			managed := parseManagedVersions(pom)
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				cga := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				if cv == "unknown" {
					if mv, ok := managed[cga]; ok && mv != "" {
						cv = mv
					}
				}
				key := cga + "@" + cv
				if visited[key] {
					continue
				}
				visited[key] = true
				child := &GradleDependencyNode{
					Name:            cga,
					OriginalVersion: cv,
					EffectiveVer:    cv,
					Parent:          it.ga + ":" + eff,
					TopLevel:        it.dn.TopLevel,
				}
				it.dn.Transitive = append(it.dn.Transitive, child)
				queue = append(queue, struct {
					ga string
					ov string
					dn *GradleDependencyNode
				}{cga, cv, child})
			}
		}
		var flat []FlatDep
		for _, root := range roots {
			flattenGradleNode(root, &flat)
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

// ----------------------------------------------------------------------
// 9) FINAL TEMPLATE
// ----------------------------------------------------------------------

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

<h2>Summary</h2>
<p>{{.Summary}}</p>

{{range .PomSections}}
<h2>POM Dependencies</h2>
<p>File path: {{.FilePath}}</p>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfoURL}}" target="_blank">Link</a></td>
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
<h2>TOML Dependencies</h2>
<p>File path: {{.FilePath}}</p>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfoURL}}" target="_blank">Link</a></td>
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
<h2>Gradle Dependencies</h2>
<p>File path: {{.FilePath}}</p>
{{if eq (len .Flattened) 0}}
<p>No dependencies found in {{.FilePath}}.</p>
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
  <td class="{{if eq .License "Unknown"}}unknown{{else if isCopyleft .License}}copyleft{{else}}non-copyleft{{end}}">
    {{.License}}
  </td>
  <td>{{.Parent}}</td>
  <td>{{.TopLevel}}</td>
  <td>{{.Language}}</td>
  <td><a href="{{.RepoInfoURL}}" target="_blank">Link</a></td>
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

// We'll define minimal BFS containers for the final merges
type pomHTMLSection struct {
	FilePath  string
	Flattened []FlatDep
	TreeHTML  template.HTML
}
type tomlHTMLSection struct {
	FilePath  string
	Flattened []FlatDep
	TreeHTML  template.HTML
}
type gradleHTMLSection struct {
	FilePath  string
	Flattened []FlatDep
	TreeHTML  template.HTML
}

func main() {
	// Start concurrency BFS
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	//------------------------------------------------------------------
	// 1) POM
	//------------------------------------------------------------------
	pomFiles, _ := findAllPOMFiles(".")
	var rawPoms []PomReportSection
	var finalPom []pomHTMLSection
	var totalPomTop int

	for _, pf := range pomFiles {
		depMap, err := parseOneLocalPOMFile(pf)
		if err != nil {
			fmt.Printf("Error parse POM %s => %v\n", pf, err)
			continue
		}
		totalPomTop += len(depMap)
		rawPoms = append(rawPoms, PomReportSection{pf, depMap, nil, nil})
	}
	buildTransitiveClosureForPOM(rawPoms)
	for _, r := range rawPoms {
		sb := &strings.Builder{}
		sb.WriteString(buildPOMTreesHTML(r.DependencyTree))
		finalPom = append(finalPom, pomHTMLSection{
			FilePath:  r.FilePath,
			Flattened: r.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	//------------------------------------------------------------------
	// 2) TOML
	//------------------------------------------------------------------
	tomlFiles, _ := findTOMLFile(".")
	var rawTomls []TomlReportSection
	var finalTomls []tomlHTMLSection
	var totalTomlTop int

	for _, tf := range tomlFiles {
		depMap, err := parseTOMLFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML %s => %v\n", tf, err)
			continue
		}
		totalTomlTop += len(depMap)
		rawTomls = append(rawTomls, TomlReportSection{tf, depMap, nil, nil})
	}
	buildTransitiveClosureForToml(rawTomls)
	for _, t := range rawTomls {
		sb := &strings.Builder{}
		sb.WriteString(buildPOMTreesHTML(t.DependencyTree)) // reuse BFS expansions
		finalTomls = append(finalTomls, tomlHTMLSection{
			FilePath:  t.FilePath,
			Flattened: t.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	//------------------------------------------------------------------
	// 3) Gradle
	//------------------------------------------------------------------
	gradleFiles, _ := findBuildGradleFiles(".")
	var rawGradles []GradleReportSection
	var finalGradles []gradleHTMLSection
	var totalGradleTop int

	for _, gf := range gradleFiles {
		dmap, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle %s => %v\n", gf, err)
			continue
		}
		totalGradleTop += len(dmap)
		rawGradles = append(rawGradles, GradleReportSection{gf, dmap, nil, nil})
	}
	buildTransitiveClosureForGradle(rawGradles)
	for _, g := range rawGradles {
		sb := &strings.Builder{}
		sb.WriteString(buildGradleTreesHTML(g.DependencyTree))
		finalGradles = append(finalGradles, gradleHTMLSection{
			FilePath:  g.FilePath,
			Flattened: g.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	//------------------------------------------------------------------
	// Close BFS concurrency
	//------------------------------------------------------------------
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	//------------------------------------------------------------------
	// Summaries
	//------------------------------------------------------------------
	// Count how many copyleft across all BFS
	copyleftCount := 0
	for _, p := range rawPoms {
		for _, f := range p.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, t := range rawTomls {
		for _, f := range t.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	for _, g := range rawGradles {
		for _, f := range g.Flattened {
			if isCopyleft(f.License) {
				copyleftCount++
			}
		}
	}
	summary := fmt.Sprintf("Maven top-level: %d, TOML top-level: %d, Gradle top-level: %d, Copyleft: %d",
		totalPomTop, totalTomlTop, totalGradleTop, copyleftCount)

	//------------------------------------------------------------------
	// Final data for template
	//------------------------------------------------------------------
	data := struct {
		Summary       string
		PomSections   []pomHTMLSection
		TomlSections  []tomlHTMLSection
		GradleSections []gradleHTMLSection
	}{
		Summary:        summary,
		PomSections:    finalPom,
		TomlSections:   finalTomls,
		GradleSections: finalGradles,
	}

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"isCopyleft": isCopyleft,
	}).Parse(finalReportTemplate)
	if err != nil {
		fmt.Printf("Template parse error => %v\n", err)
		return
	}
	out, err := os.Create("maven-multi-file-report.html")
	if err != nil {
		fmt.Printf("Create file error => %v\n", err)
		return
	}
	defer out.Close()

	if e2 := tmpl.Execute(out, data); e2 != nil {
		fmt.Printf("Template exec error => %v\n", e2)
		return
	}
	fmt.Println("maven-multi-file-report.html generated successfully!")
}

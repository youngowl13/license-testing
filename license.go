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

	// For TOML parsing
	"github.com/pelletier/go-toml"
)

// ------------------------------------------------------------------------------------
// 1) SHARED CONFIG / GLOBALS
// ------------------------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"
	pomWorkerCount   = 10
	fetchTimeout     = 30 * time.Second
)

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map
	parentVisit sync.Map

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

// ------------------------------------------------------------------------------------
// 2) DATA STRUCTURES
// ------------------------------------------------------------------------------------

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
	XMLName        xml.Name `xml:"project"`
	GroupID        string   `xml:"groupId"`
	ArtifactID     string   `xml:"artifactId"`
	Version        string   `xml:"version"`
	Parent         POMParent
	Licenses       []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
}

// BFS concurrency
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
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

// BFS node for POM/TOML
type DependencyNode struct {
	Name            string // group/artifact
	OriginalVersion string // from source file (could be "unknown")
	EffectiveVer    string // actual version used for BFS (maybe "latest")
	License         string
	Copyleft        bool
	Parent          string
	TopLevel        string
	Transitive      []*DependencyNode

	SourceLink string // actual POM link from which we derived license
}

// BFS node for Gradle
type GradleDependencyNode struct {
	Name            string
	OriginalVersion string
	EffectiveVer    string
	License         string
	Copyleft        bool
	Parent          string
	TopLevel        string
	Transitive      []*GradleDependencyNode

	SourceLink string
}

// For final table
type FlatDep struct {
	Name     string
	Version  string
	License  string
	Details  string
	Language string
	Parent   string
	TopLevel string
}

// skip test/provided/system scopes
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

// detectLicense => see if it matches known SPDx or fallback
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
	// 1) SPDx check
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// 2) keyword fallback
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
	up := strings.ToUpper(name)
	for _, k := range keywords {
		if strings.Contains(up, strings.ToUpper(k)) {
			return true
		}
	}
	return false
}

// The big fallback logic: if the version is "unknown", we fetch getLatestVersion()
func fallbackVersionIfUnknown(g, a, orig string) (string, error) {
	if strings.ToLower(orig) != "unknown" {
		// no fallback needed
		return orig, nil
	}
	latest, err := getLatestVersion(g, a)
	if err != nil {
		return "unknown", err
	}
	return latest, nil
}

// concurrency BFS fetch
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	req := fetchRequest{GroupID: g, ArtifactID: a, Version: v, ResultChan: make(chan fetchResult, 1)}
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// retrieveOrLoadPOM => from cache or remote => merges parents
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	pom, err := fetchRemotePOM(g, a, v)
	if err != nil {
		return nil, err
	}
	if pom != nil {
		pomCache.Store(key, pom)
		if pom.GroupID == "" {
			pom.GroupID = pom.Parent.GroupID
		}
		if pom.Version == "" {
			pom.Version = pom.Parent.Version
		}
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
	for _, v := range outMap {
		merged = append(merged, v)
	}
	sort.Slice(merged, func(i, j int) bool {
		return merged[i].GroupID < merged[j].GroupID
	})
	return merged
}

// fetchRemotePOM => tries central, then google
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

func parseVersionRange(v string) string {
	v = strings.TrimSpace(v)
	if (strings.HasPrefix(v, "[") || strings.HasPrefix(v, "(")) && strings.Contains(v, ",") {
		trim := strings.Trim(v, "[]() ")
		parts := strings.Split(trim, ",")
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

// getLatestVersion => tries central, then google
func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v, e := fetchLatestVersionFromURL(mavenURL); e == nil && v != "" {
		return v, nil
	}
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	if v2, e2 := fetchLatestVersionFromURL(googleURL); e2 == nil && v2 != "" {
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
	return "", fmt.Errorf("no version found in metadata at %s", url)
}

func splitGA(ga string) (string, string) {
	p := strings.SplitN(ga, "/", 2)
	if len(p) != 2 {
		return "", ""
	}
	return p[0], p[1]
}

// buildPOMLink => actual .pom file link for BFS
func buildPOMLink(g, a, v string) string {
	groupPath := strings.ReplaceAll(g, ".", "/")
	return fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
}

// buildGoogleLink => fallback if central 404
func buildGoogleLink(g, a, v string) string {
	groupPath := strings.ReplaceAll(g, ".", "/")
	return fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
}

// -----------------------------------------------------------------------------
// 3) BFS FOR POM & TOML
// -----------------------------------------------------------------------------

type PomReportSection struct {
	FilePath       string
	DirectDeps     map[string]string
	DependencyTree []*DependencyNode
	Flattened      []FlatDep
}

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

func buildTransitiveClosureForPOM(secs []PomReportSection) {
	for i := range secs {
		sec := &secs[i]
		visited := make(map[string]bool)
		var roots []*DependencyNode
		var queue []struct {
			ga    string
			ov    string // original version
			depth int
			node  *DependencyNode
		}
		for ga, ver := range sec.DirectDeps {
			n := &DependencyNode{
				Name:            ga,
				OriginalVersion: ver,
				EffectiveVer:    ver, // might be replaced
				Parent:          "direct",
				TopLevel:        ga,
			}
			roots = append(roots, n)
			key := ga + "@" + ver
			visited[key] = true
			queue = append(queue, struct {
				ga    string
				ov    string
				depth int
				node  *DependencyNode
			}{ga, ver, 1, n})
		}

		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			g, a := splitGA(it.ga)
			if g == "" || a == "" {
				continue
			}
			eff, e2 := fallbackVersionIfUnknown(g, a, it.ov)
			it.node.EffectiveVer = eff
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
			// set license
			lic := detectLicense(pom)
			it.node.License = lic
			it.node.Copyleft = isCopyleft(lic)
			it.node.SourceLink = buildPOMLink(g, a, eff) // actual .pom URL

			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				cga := d.GroupID + "/" + d.ArtifactID
				ov := d.Version
				if ov == "" {
					ov = "unknown"
				}
				ck := cga + "@" + ov
				if visited[ck] {
					continue
				}
				visited[ck] = true
				child := &DependencyNode{
					Name:            cga,
					OriginalVersion: ov,
					EffectiveVer:    ov,
					Parent:          fmt.Sprintf("%s:%s", it.ga, eff),
					TopLevel:        it.node.TopLevel,
				}
				it.node.Transitive = append(it.node.Transitive, child)
				queue = append(queue, struct {
					ga    string
					ov    string
					depth int
					node  *DependencyNode
				}{cga, ov, it.depth + 1, child})
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

func flattenPOMNode(n *DependencyNode, out *[]FlatDep) {
	details := buildPOMLinkFromNode(n)
	ver := n.OriginalVersion
	if strings.ToLower(ver) == "unknown" && n.EffectiveVer != "unknown" {
		ver = fmt.Sprintf("missing in source => %s", n.EffectiveVer)
	}
	fd := FlatDep{
		Name:     n.Name,
		Version:  ver,
		License:  n.License,
		Details:  details,
		Language: "maven",
		Parent:   n.Parent,
		TopLevel: n.TopLevel,
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenPOMNode(c, out)
	}
}

// buildPOMLinkFromNode => if BFS ended up using google mirror, we might do that. For simplicity, we always do maven central?
func buildPOMLinkFromNode(n *DependencyNode) string {
	g, a := splitGA(n.Name)
	if n.EffectiveVer == "" || strings.ToLower(n.EffectiveVer) == "unknown" {
		// fallback
		return fmt.Sprintf("https://repo1.maven.org/maven2/%s", n.Name)
	}
	groupPath := strings.ReplaceAll(g, ".", "/")
	return fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, n.EffectiveVer, a, n.EffectiveVer)
}

// -----------------------------------------------------------------------------
// 4) TOML logic
// -----------------------------------------------------------------------------

type TomlReportSection struct {
	FilePath       string
	DirectDeps     map[string]string
	DependencyTree []*DependencyNode
	Flattened      []FlatDep
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
		return nil, err
	}
	versions, err := loadTomlVersions(tree)
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
		actualVer, found := versions[versionRef]
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
		switch v := val.(type) {
		case string:
			res[k] = v
		}
	}
	return res, nil
}

func buildTransitiveClosureForToml(secs []TomlReportSection) {
	for i := range secs {
		sec := &secs[i]
		visited := make(map[string]bool)
		var roots []*DependencyNode
		var queue []struct {
			ga    string
			ov    string
			depth int
			node  *DependencyNode
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
			key := ga + "@" + ver
			visited[key] = true
			queue = append(queue, struct {
				ga    string
				ov    string
				depth int
				node  *DependencyNode
			}{ga, ver, 1, n})
		}
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			g, a := splitGA(it.ga)
			if g == "" || a == "" {
				continue
			}
			eff, e2 := fallbackVersionIfUnknown(g, a, it.ov)
			it.node.EffectiveVer = eff
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
			it.node.License = lic
			it.node.Copyleft = isCopyleft(lic)
			it.node.SourceLink = buildPOMLink(g, a, eff)

			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				cga := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				ck := cga + "@" + cv
				if visited[ck] {
					continue
				}
				visited[ck] = true
				child := &DependencyNode{
					Name:            cga,
					OriginalVersion: cv,
					EffectiveVer:    cv,
					Parent:          fmt.Sprintf("%s:%s", it.ga, eff),
					TopLevel:        it.node.TopLevel,
				}
				it.node.Transitive = append(it.node.Transitive, child)
				queue = append(queue, struct {
					ga    string
					ov    string
					depth int
					node  *DependencyNode
				}{cga, cv, it.depth + 1, child})
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

// ------------------------------------------------------------------------------------
// 5) GRADLE BFS
// ------------------------------------------------------------------------------------

type GradleReportSection struct {
	FilePath       string
	Dependencies   map[string]ExtendedDepInfo
	DependencyTree []*GradleDependencyNode
	Flattened      []FlatDep
}

type ExtendedDepInfo struct {
	Display string
	Lookup  string
	Parent  string
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

// parse def var= "1.2.3" and lines like compile "group:artifact:version"
func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	dat, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
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
		deps[key] = ExtendedDepInfo{Display: version, Lookup: version, Parent: "direct"}
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

func buildTransitiveClosureForGradle(gsec []GradleReportSection) {
	for i := range gsec {
		sec := &gsec[i]
		visited := make(map[string]bool)
		nodeMap := make(map[string]*GradleDependencyNode)
		var roots []*GradleDependencyNode
		var queue []struct {
			ga  string
			ov  string
			dep *GradleDependencyNode
		}
		// BFS init from direct
		for depKey, info := range sec.Dependencies {
			gaVer := strings.SplitN(depKey, "@", 2)
			ga := gaVer[0]
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
			nodeMap[depKey] = n
			queue = append(queue, struct {
				ga  string
				ov  string
				dep *GradleDependencyNode
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
			it.dep.EffectiveVer = eff
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
			it.dep.License = lic
			it.dep.Copyleft = isCopyleft(lic)
			it.dep.SourceLink = buildPOMLink(g, a, eff)

			// parse sub-deps
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
					// see if managed has it
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
					Parent:          fmt.Sprintf("%s:%s", it.ga, eff),
					TopLevel:        it.dep.TopLevel,
				}
				it.dep.Transitive = append(it.dep.Transitive, child)
				queue = append(queue, struct {
					ga  string
					ov  string
					dep *GradleDependencyNode
				}{cga, cv, child})
			}
		}

		// Flatten
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

func flattenGradleNode(n *GradleDependencyNode, out *[]FlatDep) {
	details := buildGradleLinkFromNode(n)
	ver := n.OriginalVersion
	if strings.ToLower(ver) == "unknown" && n.EffectiveVer != "unknown" {
		ver = fmt.Sprintf("missing in source => %s", n.EffectiveVer)
	}
	fd := FlatDep{
		Name:     n.Name,
		Version:  ver,
		License:  n.License,
		Details:  details,
		Language: "gradle",
		Parent:   n.Parent,
		TopLevel: n.TopLevel,
	}
	*out = append(*out, fd)
	for _, c := range n.Transitive {
		flattenGradleNode(c, out)
	}
}

func buildGradleLinkFromNode(n *GradleDependencyNode) string {
	g, a := splitGA(n.Name)
	if n.EffectiveVer == "" || strings.ToLower(n.EffectiveVer) == "unknown" {
		return fmt.Sprintf("https://repo1.maven.org/maven2/%s", n.Name)
	}
	groupPath := strings.ReplaceAll(g, ".", "/")
	return fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, n.EffectiveVer, a, n.EffectiveVer)
}

// parseManagedVersions => merges from pom.DependencyMgmt
func parseManagedVersions(pom *MavenPOM) map[string]string {
	out := make(map[string]string)
	for _, d := range pom.DependencyMgmt.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		if d.Version != "" {
			key := d.GroupID + "/" + d.ArtifactID
			out[key] = parseVersionRange(d.Version)
		}
	}
	return out
}

// ------------------------------------------------------------------------------------
// 6) FINAL REPORT
// ------------------------------------------------------------------------------------

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
  <th>Details (.pom)</th>
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
  <th>Details (.pom)</th>
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
  <th>Details (.pom)</th>
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

// ------------------------------------------------------------------------------------
// MAIN
// ------------------------------------------------------------------------------------

func main() {
	// Worker pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	// 1) POM
	pomFiles, _ := findAllPOMFiles(".")
	var pomSections []PomReportSection
	for _, pf := range pomFiles {
		depMap, err := parseOneLocalPOMFile(pf)
		if err != nil {
			fmt.Printf("Error parse POM %s => %v\n", pf, err)
			continue
		}
		pomSections = append(pomSections, PomReportSection{pf, depMap, nil, nil})
	}
	buildTransitiveClosureForPOM(pomSections)

	// 2) TOML
	tomlFiles, _ := findTOMLFile(".")
	var tomlSections []TomlReportSection
	for _, tf := range tomlFiles {
		depMap, err := parseTOMLFile(tf)
		if err != nil {
			fmt.Printf("Error parse TOML %s => %v\n", tf, err)
			continue
		}
		tomlSections = append(tomlSections, TomlReportSection{tf, depMap, nil, nil})
	}
	buildTransitiveClosureForToml(tomlSections)

	// 3) Gradle
	gradleFiles, _ := findBuildGradleFiles(".")
	var gradleSections []GradleReportSection
	for _, gf := range gradleFiles {
		dmap, err := parseBuildGradleFile(gf)
		if err != nil {
			fmt.Printf("Error parse Gradle %s => %v\n", gf, err)
			continue
		}
		gradleSections = append(gradleSections, GradleReportSection{gf, dmap, nil, nil})
	}
	buildTransitiveClosureForGradle(gradleSections)

	// close concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// BFS expansions => final HTML
	type pomHTMLSection struct {
		FilePath  string
		Flattened []FlatDep
		TreeHTML  template.HTML
	}
	var finalPom []pomHTMLSection
	for _, psec := range pomSections {
		var sb strings.Builder
		sb.WriteString(buildPOMTreesHTML(psec.DependencyTree))
		finalPom = append(finalPom, pomHTMLSection{
			FilePath:  psec.FilePath,
			Flattened: psec.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	type tomlHTMLSection struct {
		FilePath  string
		Flattened []FlatDep
		TreeHTML  template.HTML
	}
	var finalToml []tomlHTMLSection
	for _, tsec := range tomlSections {
		var sb strings.Builder
		sb.WriteString(buildPOMTreesHTML(tsec.DependencyTree))
		finalToml = append(finalToml, tomlHTMLSection{
			FilePath:  tsec.FilePath,
			Flattened: tsec.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	type gradleHTMLSection struct {
		FilePath  string
		Flattened []FlatDep
		TreeHTML  template.HTML
	}
	var finalGradle []gradleHTMLSection
	for _, gsec := range gradleSections {
		var sb strings.Builder
		sb.WriteString(buildGradleTreesHTML(gsec.DependencyTree))
		finalGradle = append(finalGradle, gradleHTMLSection{
			FilePath:  gsec.FilePath,
			Flattened: gsec.Flattened,
			TreeHTML:  template.HTML(sb.String()),
		})
	}

	// Data for template
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

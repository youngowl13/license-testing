package main

import (
	"encoding/xml"
	"fmt"
	"html/template"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"

	"github.com/pelletier/go-toml"
)

// License represents the license details from a POM file
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// MavenPOM represents the structure of a POM file
type MavenPOM struct {
	XMLName  xml.Name  `xml:"project"`
	Licenses []License `xml:"licenses>license"`
}

// findTOMLFile searches for a TOML file in the current directory recursively
func findTOMLFile(root string) (string, error) {
	var tomlFile string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
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

// parseTOMLFile parses a TOML file and extracts dependencies and their versions
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
			continue
		}

		lib, ok := libTree.(*toml.Tree)
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

		version, ok := versions[versionRef]
		if !ok {
			version = "unknown"
		}

		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			continue
		}
		group := parts[0]
		name := parts[1]

		dependencyKey := fmt.Sprintf("%s/%s", group, name)
		dependencies[dependencyKey] = version
	}

	return dependencies, nil
}

// loadVersions loads and flattens the versions table into a map
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
		}
	}

	return versions, nil
}

// fetchPOMFromURL fetches and unmarshals the POM from the given URL
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, fmt.Errorf("error fetching POM from %s: %v", url, err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("error fetching POM from %s: status code %d", url, resp.StatusCode)
	}

	data, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("error reading POM from %s: %v", url, err)
	}

	var pom MavenPOM
	err = xml.Unmarshal(data, &pom)
	if err != nil {
		return nil, fmt.Errorf("error unmarshalling POM from %s: %v", url, err)
	}

	return &pom, nil
}

// fetchPOM fetches the POM file concurrently from Maven Central and Google's Android Maven Repository
func fetchPOM(groupID, artifactID, version string) (string, string, *MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	type result struct {
		pom       *MavenPOM
		sourceURL string
		err       error
	}
	resultCh := make(chan result, 2)

	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(mavenURL)
		resultCh <- result{pom, mavenURL, err}
	}()

	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(googleURL)
		resultCh <- result{pom, googleURL, err}
	}()

	go func() {
		wg.Wait()
		close(resultCh)
	}()

	for res := range resultCh {
		if res.err == nil {
			return res.sourceURL, "", res.pom, nil
		}
	}

	return "", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), nil, fmt.Errorf("POM not found in Maven Central or Google's Android Maven Repository for %s:%s:%s", groupID, artifactID, version)
}

// isCopyleft determines if a license is copyleft based on its name or common abbreviations
func isCopyleft(licenseName string) bool {
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "Affero GPL", "GNU General Public License", "GNU Lesser General Public License",
		"AGPL", "MPL", "Mozilla Public License", "EPL", "Eclipse Public License", "CPL", "CDDL",
		"Common Development and Distribution License", "EUPL", "European Union Public License", "CeCILL",
	}
	licenseNameUpper := strings.ToUpper(licenseName)
	for _, keyword := range copyleftKeywords {
		if strings.Contains(licenseNameUpper, strings.ToUpper(keyword)) {
			return true
		}
	}
	return false
}

// generateHTMLReport generates an HTML report of the dependencies and their licenses
func generateHTMLReport(dependencies map[string]string) error {
	outputDir := "./license-checker"
	if _, err := os.Stat(outputDir); os.IsNotExist(err) {
		os.Mkdir(outputDir, 0755)
	}

	htmlTemplate := `<!DOCTYPE html>
<html>
<head>
	<title>Dependency License Report</title>
	<style>
		body { font-family: Arial, sans-serif; }
		h1 { color: #2c3e50; }
		table { width: 100%; border-collapse: collapse; }
		th, td { padding: 8px; border: 1px solid #ddd; }
		th { background-color: #f0f0f0; }
		tr:nth-child(even) { background-color: #f9f9f9; }
		a { color: #3498db; text-decoration: none; }
		a:hover { text-decoration: underline; }
		.copyleft { background-color: #ffdddd; }
		.non-copyleft { background-color: #ddffdd; }
		.unknown-license { background-color: #ffffdd; }
	</style>
</head>
<body>
	<h1>Dependency License Report</h1>
	<table>
		<thead>
			<tr>
				<th>Dependency</th>
				<th>Version</th>
				<th>License</th>
				<th>License Details</th>
				<th>POM Source</th>
			</tr>
		</thead>
		<tbody>
			{{range $dep, $version := .}}
			{{ $group, $artifact, _ := splitDependency $dep }}
			{{ $licenseName, $licenseURL, $sourceURL := getLicenseInfo $group $artifact $version }}
			<tr class="{{if eq $licenseName "Unknown"}}unknown-license{{else if isCopyleft $licenseName}}copyleft{{else}}non-copyleft{{end}}">
				<td>{{$dep}}</td>
				<td>{{$version}}</td>
				<td>{{$licenseName}}</td>
				<td><a href="{{$licenseURL}}" target="_blank">View Details</a></td>
				<td><a href="{{$sourceURL}}" target="_blank">View POM</a></td>
			</tr>
			{{end}}
		</tbody>
	</table>
</body>
</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"isCopyleft": isCopyleft,
	}).Parse(htmlTemplate)
	if err != nil {
		return fmt.Errorf("error creating template: %v", err)
	}

	reportPath := filepath.Join(outputDir, "dependency-license-report.html")
	file, err := os.Create(reportPath)
	if err != nil {
		return fmt.Errorf("error creating report file: %v", err)
	}
	defer file.Close()

	err = tmpl.Execute(file, dependencies)
	if err != nil {
		return fmt.Errorf("error generating report: %v", err)
	}

	fmt.Println("✅ License report successfully generated at", reportPath)
	return nil
}

func main() {
	tomlFilePath, err := findTOMLFile(".")
	if err != nil {
		fmt.Printf("Error finding TOML file: %v\n", err)
		os.Exit(1)
	}

	dependencies, err := parseTOMLFile(tomlFilePath)
	if err != nil {
		fmt.Printf("Error parsing TOML file: %v\n", err)
		os.Exit(1)
	}

	err = generateHTMLReport(dependencies)
	if err != nil {
		fmt.Printf("Error generating report: %v\n", err)
		os.Exit(1)
	}
}

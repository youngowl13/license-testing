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

	versionsTree := tree.Get("versions")
	librariesTree := tree.Get("libraries")

	var versions map[string]interface{}
	if versionsTree != nil {
		versions = versionsTree.(*toml.Tree).ToMap()
	}

	var libraries map[string]interface{}
	if librariesTree != nil {
		libraries = librariesTree.(*toml.Tree).ToMap()
	}

	for _, value := range libraries {
		lib := value.(map[string]interface{})
		group, ok := lib["group"].(string)
		if !ok {
			fmt.Println("Warning: 'group' not found for a library entry in TOML file.")
			continue
		}
		name, ok := lib["name"].(string)
		if !ok {
			fmt.Println("Warning: 'name' not found for a library entry in TOML file.")
			continue
		}
		versionRef, ok := lib["version.ref"].(string)
		if !ok {
			fmt.Println("Warning: 'version.ref' not found for a library entry in TOML file.")
			continue
		}

		if versions == nil {
			fmt.Println("Warning: 'versions' table not found in TOML file.")
			continue
		}

		version, ok := versions[versionRef].(string)
		if !ok {
			fmt.Println("Warning: version reference not found in 'versions' table.")
			continue
		}
		dependencies[filepath.Join(group, name)] = version
	}

	return dependencies, nil
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
func fetchPOM(groupID, artifactID, version string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	type result struct {
		pom *MavenPOM
		err error
	}
	resultCh := make(chan result, 2)

	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(mavenURL)
		resultCh <- result{pom, err}
	}()

	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(googleURL)
		resultCh <- result{pom, err}
	}()

	go func() {
		wg.Wait()
		close(resultCh)
	}()

	for res := range resultCh {
		if res.err == nil {
			return res.pom, nil
		}
	}

	return nil, fmt.Errorf("POM not found in Maven Central or Google's Android Maven Repository for %s:%s:%s", groupID, artifactID, version)
}

// getLicenseInfo fetches the license details for a dependency
func getLicenseInfo(groupID, artifactID, version string) (string, string) {
	pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version)
	}
	return pom.Licenses[0].Name, pom.Licenses[0].URL
}

// splitDependency splits a dependency string into groupID and artifactID
func splitDependency(dep string) (string, string, error) {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return "", "", fmt.Errorf("invalid dependency format: %s", dep)
	}
	return parts[0], parts[1], nil
}

// Returns a combined string of groupID and artifactID.
func splitDependencyWrapper(dep string) string {
	groupID, artifactID, err := splitDependency(dep)
	if err != nil {
		fmt.Printf("Warning: Error splitting dependency '%s': %v\n", dep, err)
		return ""
	}
	return groupID + "/" + artifactID
}

// getLicenseInfoWrapper is a wrapper for getLicenseInfo for use in the template.
func getLicenseInfoWrapper(dep string) (string, string) {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return "Unknown", "URL Not Found"
	}
	groupID, artifactID := parts[0], parts[1]

	licenseName, licenseURL := getLicenseInfo(groupID, artifactID, "unknown") // Replace "unknown" with a proper version if available
	return licenseName, licenseURL
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
			th, td { text-align: left; padding: 8px; border: 1px solid #ddd; }
			th { background-color: #f0f0f0; }
			tr:nth-child(even) { background-color: #f9f9f9; }
			a { color: #3498db; text-decoration: none; }
			a:hover { text-decoration: underline; }
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
					<th>Details</th>
				</tr>
			</thead>
			<tbody>
				{{range $dep, $version := .}}
				<tr>
					<td>{{ splitDependencyWrapper $dep }}</td>
					<td>{{ $version }}</td>
					{{ $license, $url := getLicenseInfoWrapper $dep }}
					<td>{{ $license }}</td>
					<td><a href="{{ $url }}" target="_blank">View Details</a></td>
				</tr>
				{{end}}
			</tbody>
		</table>
	</body>
	</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"splitDependencyWrapper": splitDependencyWrapper,
		"getLicenseInfoWrapper":  getLicenseInfoWrapper,
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

// main is the entry point of the program
func main() {
	tomlFilePath, err := findTOMLFile(".")
	if err != nil {
		fmt.Printf("Error finding TOML file: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("Found TOML file at: %s\n", tomlFilePath)

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

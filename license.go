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
	if tomlFile == "" {
		return "", fmt.Errorf("no .toml file found")
	}
	return tomlFile, err
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
			continue // Skip this entry and proceed with the next one
		}
		name, ok := lib["name"].(string)
		if !ok {
			fmt.Println("Warning: 'name' not found for a library entry in TOML file.")
			continue // Skip this entry and proceed with the next one
		}
		versionRef, ok := lib["version.ref"].(string)
		if !ok {
			fmt.Println("Warning: 'version.ref' not found for a library entry in TOML file.")
			continue // Skip this entry and proceed with the next one
		}

		// Accessing versions map safely
		if versions == nil {
			fmt.Println("Warning: 'versions' table not found in TOML file.")
			continue // Skip this entry and proceed with the next one
		}

		version, ok := versions[versionRef].(string)
		if !ok {
			fmt.Println("Warning: version reference not found in 'versions' table.")
			continue // Skip this entry and proceed with the next one
		}
		dependencies[filepath.Join(group, name)] = version
	}

	return dependencies, nil
}

// fetchPOM fetches the POM file from Maven Central or Google's Android Maven Repository
func fetchPOM(groupID, artifactID, version string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	// Try Maven Central first
	pom, err := fetchPOMFromURL(mavenURL)
	if err == nil {
		return pom, nil
	}

	// Then try Google's Android Maven Repository
	pom, err = fetchPOMFromURL(googleURL)
	if err == nil {
		return pom, nil
	}

	return nil, fmt.Errorf("POM not found in Maven Central or Google's Android Maven Repository for %s:%s:%s", groupID, artifactID, version)
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

// getLicenseInfo fetches the license details for a dependency
func getLicenseInfo(groupID, artifactID, version string) (string, string) {
	pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version)
	}
	return pom.Licenses[0].Name, pom.Licenses[0].URL
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
                    <td>{{$dep}}</td>
                    <td>{{$version}}</td>
                    {{ $groupID, $artifactID, $err := splitDependency $dep }}
                    {{ if $err }}
                    <td colspan="2">Error: {{$err}}</td>
                    {{ else }}
                    {{ $license, $url := getLicenseInfo $groupID $artifactID $version }}
                    <td>{{$license}}</td>
                    <td><a href="{{$url}}" target="_blank">View Details</a></td>
                    {{ end }}
                </tr>
                {{end}}
            </tbody>
        </table>
    </body>
    </html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"splitDependency": func(dep string) (string, string, error) {
			parts := strings.Split(dep, "/")
			if len(parts) != 2 {
				return "", "", fmt.Errorf("invalid dependency format: %s", dep)
			}
			return parts[0], parts[1], nil
		},
		"getLicenseInfo": getLicenseInfo,
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

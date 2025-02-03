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

// ... (other functions: License, MavenPOM, findTOMLFile, parseTOMLFile, fetchPOMFromURL, fetchPOM, splitDependency)

// getLicenseInfo fetches the license details for a dependency
func getLicenseInfo(groupID, artifactID, version string) (string, string) {
	pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version)
	}
	return pom.Licenses[0].Name, pom.Licenses[0].URL
}

// getLicenseInfoWrapper is a wrapper for getLicenseInfo for use in the template.
func getLicenseInfoWrapper(dependency string) (string, string) {
	parts := strings.Split(dependency, "/")
	if len(parts) != 2 {
		return "Unknown", "#" // Return default values or handle error
	}
	groupID, artifactID := parts[0], parts[1]
	// Assuming you have a way to get the version, or it's not needed here.
	// Replace "version" with actual version if needed.
	return getLicenseInfo(groupID, artifactID, "unknown")
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
		return "" // Return empty string on error
	}
	return groupID + "/" + artifactID
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
						<td>{{ $dep }}</td>
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

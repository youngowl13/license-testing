package main

import (
	"bytes"
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

// License represents the license details from a POM file.
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// MavenPOM represents the structure of a Maven POM file.
type MavenPOM struct {
	XMLName  xml.Name  `xml:"project"`
	Licenses []License `xml:"licenses>license"`
}

// findTOMLFile searches for a TOML file in the current directory recursively.
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

// parseTOMLFile parses a TOML file and extracts dependencies and their versions.
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

		version, ok := versions[versionRef]
		if !ok {
			fmt.Printf("Warning: version reference '%s' not found in 'versions' table for library '%s'.\n", versionRef, libKey)
			version = "unknown"
		}

		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			fmt.Printf("Warning: invalid module format for library entry '%s'.\n", libKey)
			continue
		}
		group := parts[0]
		name := parts[1]

		dependencyKey := fmt.Sprintf("%s/%s", group, name)
		dependencies[dependencyKey] = version
	}

	return dependencies, nil
}

// loadVersions loads and flattens the versions table into a map.
func loadVersions(tree *toml.Tree) (map[string]string, error) {
	versions := make(map[string]string)
	versionsTree := tree.Get("versions")
	if versionsTree == nil {
		return versions, nil // Return empty map if no versions table found.
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

// fetchPOMFromURL fetches and unmarshals the POM from the given URL.
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

// fetchPOM concurrently attempts to fetch the POM file from Maven Central and Google.
// For Google artifacts, the POM file is fetched using the dl.google.com endpoint,
// but the project "View Details" link will point to maven.google.com.
func fetchPOM(groupID, artifactID, version string) (string, string, *MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")

	// URL to fetch the POM file from Maven Central.
	mavenPOMURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	// URL to fetch the POM file from Google's Maven repository.
	googlePOMURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	type result struct {
		pom        *MavenPOM
		sourceURL  string // URL used to fetch the POM file.
		projectURL string // URL used for the "View Details" link.
		err        error
	}
	resultCh := make(chan result, 2)
	var wg sync.WaitGroup
	wg.Add(2)

	// Try Maven Central.
	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(mavenPOMURL)
		// For Maven Central, the details link points to the version directory.
		projectURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, artifactID, version)
		resultCh <- result{pom, mavenPOMURL, projectURL, err}
	}()

	// Try Google's Maven repository.
	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(googlePOMURL)
		// Even though the POM is fetched from dl.google.com, use maven.google.com for the details link.
		projectURL := fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", groupID, artifactID, version)
		resultCh <- result{pom, googlePOMURL, projectURL, err}
	}()

	go func() {
		wg.Wait()
		close(resultCh)
	}()

	var finalSourceURL, finalProjectURL string
	var finalPOM *MavenPOM
	var finalError error

	for res := range resultCh {
		if res.err == nil && res.pom != nil {
			finalSourceURL = res.sourceURL
			finalProjectURL = res.projectURL
			finalPOM = res.pom
			finalError = nil
			break // Use the first successful result.
		} else {
			finalError = res.err // Capture last error if both fail.
		}
	}

	if finalPOM == nil {
		// If neither repository returned a valid POM, fallback to a Google search link.
		searchURL := fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version)
		return "", searchURL, nil, finalError
	}

	return finalSourceURL, finalProjectURL, finalPOM, nil
}

// getLicenseInfo fetches the license details for a dependency.
// On success, it returns the license name, the "View Details" link (project URL), and the POM file URL.
func getLicenseInfo(groupID, artifactID, version string) (string, string, string) {
	sourceURL, projectURL, pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), ""
	}
	return pom.Licenses[0].Name, projectURL, sourceURL
}

// splitDependency splits a dependency string (formatted as "groupID/artifactID") into its parts.
func splitDependency(dep string) (string, string, error) {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return "", "", fmt.Errorf("invalid dependency format: %s", dep)
	}
	return parts[0], parts[1], nil
}

// LicenseInfo holds the license name, the project details link, and the POM file link.
type LicenseInfo struct {
	Name       string
	URL        string // Project details link ("View Details")
	POMFileURL string // POM file link ("View POM")
}

// getLicenseInfoWrapper wraps getLicenseInfo for use in the HTML template.
func getLicenseInfoWrapper(dep, version string) LicenseInfo {
	groupID, artifactID, err := splitDependency(dep)
	if err != nil {
		fmt.Printf("Warning: Invalid dependency format '%s': %v\n", dep, err)
		return LicenseInfo{"Unknown", "", ""}
	}

	name, url, pomurl := getLicenseInfo(groupID, artifactID, version)
	return LicenseInfo{Name: name, URL: url, POMFileURL: pomurl}
}

// isCopyleft determines if a license is considered copyleft based on keywords.
// It converts both the license name and each keyword to uppercase to ensure a case-insensitive match.
func isCopyleft(licenseName string) bool {
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
	licenseNameUpper := strings.ToUpper(licenseName)
	for _, keyword := range copyleftKeywords {
		if strings.Contains(licenseNameUpper, strings.ToUpper(keyword)) {
			return true
		}
	}
	return false
}

// generateHTMLReport generates an HTML report of the dependencies and their licenses.
func generateHTMLReport(dependencies map[string]string) error {
	fmt.Println("Dependencies:", dependencies)
	outputDir := "./license-checker"
	if _, err := os.Stat(outputDir); os.IsNotExist(err) {
		os.Mkdir(outputDir, 0755)
	}

	htmlTemplate := `<!DOCTYPE html>
<html>
<head>
    <title>Kotlin Dependency License Report</title>
    <style>
        body { font-family: Arial, sans-serif; }
        h1 { color: #2c3e50; }
        table { width: 100%; border-collapse: collapse; }
        th, td { text-align: left; padding: 8px; border: 1px solid #ddd; }
        th { background-color: #f0f0f0; }
        tr:nth-child(even) { background-color: #f9f9f9; }
        a { color: #3498db; text-decoration: none; }
        a:hover { text-decoration: underline; }
        tr.copyleft { background-color: #ffdddd; }
        tr.non-copyleft { background-color: #ddffdd; }
        tr.unknown-license { background-color: #ffffdd; }
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
                <th>Project Details</th>
                <th>POM File</th>
            </tr>
        </thead>
        <tbody>
            {{range $dep, $version := .}}
            {{ $info := getLicenseInfoWrapper $dep $version }}
            {{ if eq $info.Name "Unknown" }}
                <tr class="unknown-license">
            {{ else if isCopyleft $info.Name }}
                <tr class="copyleft">
            {{ else }}
                <tr class="non-copyleft">
            {{ end }}
                <td>{{ $dep }}</td>
                <td>{{ $version }}</td>
                <td>{{ $info.Name }}</td>
                <td><a href="{{ $info.URL }}" target="_blank">View Details</a></td>
                <td><a href="{{ $info.POMFileURL }}" target="_blank">View POM</a></td>
            </tr>
            {{end}}
        </tbody>
    </table>
</body>
</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"getLicenseInfoWrapper": getLicenseInfoWrapper,
		"isCopyleft":            isCopyleft,
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

// captureOutput captures stdout and stderr to a buffer.
func captureOutput(f func()) string {
	var buf bytes.Buffer
	oldStdout := os.Stdout
	oldStderr := os.Stderr
	defer func() {
		os.Stdout = oldStdout
		os.Stderr = oldStderr
	}()

	r, w, _ := os.Pipe()
	os.Stdout = w
	os.Stderr = w

	f()

	w.Close()
	buf.ReadFrom(r)
	return buf.String()
}

// main is the entry point of the program.
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

	// Capture output for debugging.
	output := captureOutput(func() {
		err = generateHTMLReport(dependencies)
	})

	// Save output to a text file.
	outputFilePath := filepath.Join(".", "output.txt")
	err = ioutil.WriteFile(outputFilePath, []byte(output), 0644)
	if err != nil {
		fmt.Printf("Error saving output to file: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("Output saved to: %s\n", outputFilePath)
}

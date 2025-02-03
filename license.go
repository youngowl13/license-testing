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

type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

type MavenPOM struct {
	XMLName  xml.Name  `xml:"project"`
	Licenses []License `xml:"licenses>license"`
}

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
		return "", fmt.Errorf("no .toml file found in the directory tree")
	}
	return tomlFile, nil
}

func parseTOMLFile(filePath string) (map[string]string, error) {
	dependencies := make(map[string]string)
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("error loading TOML file: %v", err)
	}

	versionsTree := tree.Get("versions")
	librariesTree := tree.Get("libraries")

	var versions map[string]interface{}
	var libraries map[string]interface{}

	if versionsTree != nil {
		versions = versionsTree.(*toml.Tree).ToMap()
	}
	if librariesTree != nil {
		libraries = librariesTree.(*toml.Tree).ToMap()
	}

	for _, value := range libraries {
		lib := value.(map[string]interface{})
		group, _ := lib["group"].(string)
		name, _ := lib["name"].(string)
		versionRef, _ := lib["version.ref"].(string)
		version, _ := versions[versionRef].(string)
		dependencies[fmt.Sprintf("%s:%s", group, name)] = version
	}

	return dependencies, nil
}

func fetchPOM(groupID, artifactID, version string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	pomURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	resp, err := http.Get(pomURL)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	data, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}

	var pom MavenPOM
	err = xml.Unmarshal(data, &pom)
	return &pom, err
}

func getLicenseInfo(dependency, version string) (string, string) {
	parts := strings.Split(dependency, ":")
	if len(parts) != 2 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+license", dependency, version)
	}

	groupID, artifactID := parts[0], parts[1]
	pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+license", dependency, version)
	}
	return pom.Licenses[0].Name, pom.Licenses[0].URL
}

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
    <h1>Kotlin Dependencies</h1>
    <table>
        <thead>
            <tr>
                <th>Package</th>
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
                {{ $license, $url := getLicenseInfo $dep $version }}
                <td>{{$license}}</td>
                <td><a href="{{$url}}" target="_blank">View Details</a></td>
            </tr>
            {{end}}
        </tbody>
    </table>
</body>
</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
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

func main() {
	tomlFile, err := findTOMLFile(".")
	if err != nil {
		fmt.Printf("Error finding TOML file: %v\n", err)
		os.Exit(1)
	}

	dependencies, err := parseTOMLFile(tomlFile)
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

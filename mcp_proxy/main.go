//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/opencontainers/go-digest"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"
	"github.com/pelletier/go-toml/v2"
)

var (
	configFile = flag.String("config", "config.toml", "Path to config file")
)

type Config struct {
	TargetMCPServerURL string   `toml:"target_mcp_server_url"`
	Filters            []Filter `toml:"filter"`
}

type Filter struct {
	Method           string `toml:"method"`
	CosignIdentity   string `toml:"cosign_identity"`
	CosignOIDCIssuer string `toml:"cosign_oidc_issuer"`
	HTTPIndexPrefix  string `toml:"http_index_prefix"`
}

func main() {
	flag.Parse()

	configData, err := os.ReadFile(*configFile)
	if err != nil {
		log.Fatalf("Failed to read config file: %v", err)
	}

	var config Config
	if err := toml.Unmarshal(configData, &config); err != nil {
		log.Fatalf("Failed to parse config file: %v", err)
	}

	if config.TargetMCPServerURL == "" {
		log.Fatal("target_mcp_server_url must be provided in config")
	}

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		handleRequest(w, r, &config)
	})
	log.Println("Starting proxy server on :8080")
	if err := http.ListenAndServe(":8080", nil); err != nil {
		log.Fatalf("Failed to start server: %v", err)
	}
}

func handleRequest(w http.ResponseWriter, r *http.Request, config *Config) {
	log.Printf("handling request: %q %q", r.Method, r.URL)
	targetURL, err := url.Parse(config.TargetMCPServerURL)
	if err != nil {
		http.Error(w, fmt.Sprintf("Invalid target MCP server URL: %v", err), http.StatusInternalServerError)
		return
	}

	// Parse and inspect the incoming request
	bodyBytes, err := io.ReadAll(r.Body)
	if err != nil {
		http.Error(w, "Failed to read request body", http.StatusInternalServerError)
		return
	}
	r.Body.Close() // Close original body

	// Try to parse the body as JSON for inspection and method extraction
	var method string
	if len(bodyBytes) > 0 {
		var jsonReq map[string]interface{}
		if err := json.Unmarshal(bodyBytes, &jsonReq); err == nil {
			log.Printf("Parsed Request Body: %+v", jsonReq)
			if m, ok := jsonReq["method"].(string); ok {
				method = m
			}
		} else {
			log.Printf("Request body not JSON or malformed: %v", err)
		}
	}

	// Re-create body for forwarding
	r.Body = io.NopCloser(bytes.NewBuffer(bodyBytes))
	r.ContentLength = int64(len(bodyBytes))
	r.URL.Scheme = targetURL.Scheme
	r.URL.Host = targetURL.Host
	r.Host = targetURL.Host

	// Check for filters
	var matchedFilter *Filter
	for _, f := range config.Filters {
		if method == f.Method {
			matchedFilter = &f
			break
		}
	}

	if matchedFilter != nil && matchedFilter.CosignIdentity != "" {
		handleFilteredRequest(w, r, matchedFilter)
		return
	}

	resp, err := http.DefaultTransport.RoundTrip(r)
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to forward request: %v", err), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()

	copyHeaders(w.Header(), resp.Header)
	w.WriteHeader(resp.StatusCode)

	// Handle streaming responses (e.g. SSE)
	if f, ok := w.(http.Flusher); ok {
		buf := make([]byte, 4096)
		for {
			n, err := resp.Body.Read(buf)
			if n > 0 {
				w.Write(buf[:n])
				f.Flush()
			}
			if err != nil {
				if err != io.EOF {
					log.Printf("Error reading response body: %v", err)
				}
				break
			}
		}
	} else {
		io.Copy(w, resp.Body)
	}
}

func handleFilteredRequest(w http.ResponseWriter, r *http.Request, filter *Filter) {
	resp, err := http.DefaultTransport.RoundTrip(r)
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to forward request: %v", err), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		http.Error(w, "Failed to read response body", http.StatusInternalServerError)
		return
	}

	algo, digest := computeCanonicalDigest(body)
	subjectDigest := fmt.Sprintf("%s:%s", algo, hex.EncodeToString(digest))
	log.Printf("Response Subject Digest: %s", subjectDigest)

	// We store the content of the response to a temporary file named after the digest of the response itself.

	// Ensure temp dir exists.
	tempDir := "/tmp/mcp_proxy"
	if err := os.MkdirAll(tempDir, 0755); err != nil {
		log.Printf("Failed to create temp dir: %v", err)
	}

	// Save Subject to Cache (if needed).
	subjectPath := filepath.Join(tempDir, formatDigest(algo, digest))
	if _, err := os.Stat(subjectPath); os.IsNotExist(err) {
		if err := os.WriteFile(subjectPath, body, 0644); err != nil {
			log.Printf("Failed to write subject to cache: %v", err)
		} else {
			log.Printf("Subject cached at: %s", subjectPath)
		}
	} else {
		log.Printf("Subject already in cache: %s", subjectPath)
	}

	// See logic in /tr/endorse for an explanation of the various parts.
	endorsementVerified := false

	if filter.HTTPIndexPrefix != "" {
		indexURL := strings.TrimRight(filter.HTTPIndexPrefix, "/") + "/index.json"
		log.Printf("Fetching index from: %s", indexURL)

		index, err := fetchIndex(indexURL)
		if err != nil {
			log.Printf("Failed to fetch index: %v", err)
		} else {
			// Find endorsements for this subject.
			for _, entry := range index.Manifests {
				if entry.Annotations["tr.subject"] == subjectDigest && entry.Annotations["tr.type"] == "endorsement" {
					log.Printf("Found endorsement digest: %s", entry.Digest)

					// Prepare Endorsement Path.
					endorsementPath := filepath.Join(tempDir, entry.Digest.String())

					// Check cache for endorsement.
					if _, err := os.Stat(endorsementPath); os.IsNotExist(err) {
						// Not in cache, fetch and verify.
						blobURL := fmt.Sprintf("%s/blobs/%s/%s", strings.TrimRight(filter.HTTPIndexPrefix, "/"), entry.Digest.Algorithm(), entry.Digest.Hex())
						log.Printf("Fetching endorsement blob from: %s", blobURL)

						endorsementData, err := fetchBlob(blobURL)
						if err != nil {
							log.Printf("Failed to fetch endorsement blob: %v", err)
							continue
						}

						// Verify digest.
						if err := verifyBlobDigest(endorsementData, entry.Digest); err != nil {
							log.Printf("Endorsement digest verification failed: %v", err)
							continue
						}
						log.Printf("Endorsement digest verified.")

						// Write to cache.
						if err := os.WriteFile(endorsementPath, endorsementData, 0644); err != nil {
							log.Printf("Failed to write endorsement to cache: %v", err)
							continue
						}
						log.Printf("Endorsement cached at: %s", endorsementPath)
					} else {
						log.Printf("Endorsement already in cache: %s", endorsementPath)
					}

					// Perform cosign verification using cached files.
					log.Println("Calling cosign to verify endorsement...")
					args := []string{"verify-blob", "--bundle", endorsementPath, subjectPath}
					if filter.CosignIdentity != "" {
						args = append(args, "--certificate-identity", filter.CosignIdentity)
						// Use configured issuer or default.
						issuer := filter.CosignOIDCIssuer
						if issuer == "" {
							issuer = "https://oauth2.sigstore.dev/auth"
						}
						args = append(args, "--certificate-oidc-issuer", issuer)
					}
					cmd := exec.Command("cosign", args...)
					var cosignStdout, cosignStderr bytes.Buffer
					cmd.Stdout = &cosignStdout
					cmd.Stderr = &cosignStderr

					if err := cmd.Run(); err != nil {
						log.Printf("Cosign verification FAILED: %v", err)
						log.Printf("Cosign Stdout: %s", cosignStdout.String())
						log.Printf("Cosign Stderr: %s", cosignStderr.String())
					} else {
						log.Printf("Cosign verification PASSED for endorsement %s!", entry.Digest)
						log.Printf("Cosign Stdout: %s", cosignStdout.String())
						endorsementVerified = true
						break // Found a valid endorsement, no need to check others.
					}
				}
			}
		}
	}

	if !endorsementVerified {
		errMsg := fmt.Sprintf("Endorsement verification failed for subject digest: %s.\n"+
			"The response from the server was not endorsed by the expected identity (%s).\n"+
			"To endorse this content, please run the endorsement tool on the saved subject file:\n"+
			"endorse -file=%s -repository=<path_to_repo>\n",
			subjectDigest, filter.CosignIdentity, subjectPath)
		log.Println(errMsg)
		http.Error(w, errMsg, http.StatusForbidden)
		return
	}

	copyHeaders(w.Header(), resp.Header)
	w.Header().Set("Content-Length", fmt.Sprint(len(body)))
	w.WriteHeader(resp.StatusCode)
	w.Write(body)
}

func copyHeaders(dst, src http.Header) {
	for k, vv := range src {
		for _, v := range vv {
			dst.Add(k, v)
		}
	}
}

func computeCanonicalDigest(data []byte) (string, []byte) {
	digest := sha256.Sum256(data)
	return "sha256", digest[:]
}

func formatDigest(algo string, digest []byte) string {
	return fmt.Sprintf("%s:%s", algo, hex.EncodeToString(digest))
}

func fetchIndex(url string) (*ocispec.Index, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch index: %w", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("index lookup failed with status: %d", resp.StatusCode)
	}
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read index body: %w", err)
	}
	var index ocispec.Index
	if err := json.Unmarshal(body, &index); err != nil {
		return nil, fmt.Errorf("failed to parse index JSON: %w", err)
	}
	return &index, nil
}

func fetchBlob(url string) ([]byte, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch blob: %w", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("blob fetch failed with status: %d", resp.StatusCode)
	}
	return io.ReadAll(resp.Body)
}

func verifyBlobDigest(data []byte, expectedDigest digest.Digest) error {
	verifier := expectedDigest.Verifier()
	if _, err := verifier.Write(data); err != nil {
		return fmt.Errorf("failed to write data to verifier: %w", err)
	}
	if !verifier.Verified() {
		return fmt.Errorf("digest verification failed")
	}
	return nil
}

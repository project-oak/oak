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
	"crypto/sha256"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/opencontainers/go-digest"
	specs "github.com/opencontainers/image-spec/specs-go"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"
)

var (
	filePath = flag.String("file", "", "Path to the file to endorse")
	repoPath = flag.String("repository", ".", "Path to the endorsement repository root")
)

func main() {
	flag.Parse()
	if *filePath == "" {
		log.Fatal("-file is required")
	}

	// 1. Prepare blobs directory
	blobsDir := filepath.Join(*repoPath, "blobs", "sha256")
	if err := os.MkdirAll(blobsDir, 0755); err != nil {
		log.Fatalf("Failed to create blobs directory: %v", err)
	}

	// 2. Hash input file (Subject)
	fileData, err := os.ReadFile(*filePath)
	if err != nil {
		log.Fatalf("Failed to read file: %v", err)
	}
	subjectHash := sha256.Sum256(fileData)
	subjectDigestHex := fmt.Sprintf("%x", subjectHash)
	subjectDigest := digest.NewDigestFromEncoded(digest.SHA256, subjectDigestHex)

	// 3. Stash subject
	subjectBlobPath := filepath.Join(blobsDir, subjectDigestHex)
	if _, err := os.Stat(subjectBlobPath); os.IsNotExist(err) {
		if err := os.WriteFile(subjectBlobPath, fileData, 0644); err != nil {
			log.Fatalf("Failed to stash subject: %v", err)
		}
		log.Printf("Stashed subject to %s", subjectBlobPath)
	} else {
		log.Printf("Subject already exists at %s", subjectBlobPath)
	}

	// Prepare Subject Descriptor
	subjectMediaType := http.DetectContentType(fileData)
	subjectDesc := ocispec.Descriptor{
		MediaType: subjectMediaType,
		Digest:    subjectDigest,
		Size:      int64(len(fileData)),
		Annotations: map[string]string{
			"tr.type": "subject",
		},
	}

	// 4. Create endorsement (call cosign)
	tempBundle, err := os.CreateTemp("", "bundle-*.json")
	if err != nil {
		log.Fatalf("Failed to create temp bundle file: %v", err)
	}
	tempBundle.Close()
	defer os.Remove(tempBundle.Name())

	log.Println("Calling cosign to create endorsement... (please complete OIDC flow if prompted)")
	// Using --oidc-issuer for Sigstore Public Good instance
	cmd := exec.Command("cosign", "sign-blob", "--bundle", tempBundle.Name(), *filePath, "--oidc-issuer", "https://oauth2.sigstore.dev/auth", "--yes")
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		log.Fatalf("Cosign failed: %v", err)
	}

	// 5. Hash endorsement
	bundleData, err := os.ReadFile(tempBundle.Name())
	if err != nil {
		log.Fatalf("Failed to read generated bundle: %v", err)
	}
	endorsementHash := sha256.Sum256(bundleData)
	endorsementDigestHex := fmt.Sprintf("%x", endorsementHash)
	endorsementDigest := digest.NewDigestFromEncoded(digest.SHA256, endorsementDigestHex)

	// 6. Stash endorsement
	endorsementBlobPath := filepath.Join(blobsDir, endorsementDigestHex)
	if _, err := os.Stat(endorsementBlobPath); os.IsNotExist(err) {
		if err := os.WriteFile(endorsementBlobPath, bundleData, 0644); err != nil {
			log.Fatalf("Failed to stash endorsement: %v", err)
		}
		log.Printf("Stashed endorsement to %s", endorsementBlobPath)
	} else {
		log.Printf("Endorsement already exists at %s", endorsementBlobPath)
	}

	// Prepare Endorsement Descriptor
	endorsementDesc := ocispec.Descriptor{
		MediaType: "application/vnd.dev.sigstore.bundle+json",
		Digest:    endorsementDigest,
		Size:      int64(len(bundleData)),
		Annotations: map[string]string{
			"tr.type":    "endorsement",
			"tr.subject": subjectDigest.String(),
		},
	}

	// 7. Update index.json
	indexPath := filepath.Join(*repoPath, "index.json")
	if err := updateIndex(indexPath, subjectDesc, endorsementDesc); err != nil {
		log.Fatalf("Failed to update index: %v", err)
	}
	log.Printf("Updated index at %s", indexPath)
}

func updateIndex(path string, newEntries ...ocispec.Descriptor) error {
	var index ocispec.Index
	data, err := os.ReadFile(path)
	if err == nil {
		if err := json.Unmarshal(data, &index); err != nil {
			return fmt.Errorf("failed to parse existing index: %w", err)
		}
	} else if !os.IsNotExist(err) {
		return fmt.Errorf("failed to read index: %w", err)
	} else {
		index.Versioned = specs.Versioned{SchemaVersion: 2}
	}

	// Helper to find index of a digest
	findEntry := func(d digest.Digest) int {
		for i, m := range index.Manifests {
			if m.Digest == d {
				return i
			}
		}
		return -1
	}

	for _, entry := range newEntries {
		idx := findEntry(entry.Digest)
		if idx != -1 {
			// Update existing entry to ensure annotations and media type are correct
			index.Manifests[idx] = entry
		} else {
			// Append new entry
			index.Manifests = append(index.Manifests, entry)
		}
	}

	// Write back
	newData, err := json.MarshalIndent(index, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal index: %w", err)
	}
	return os.WriteFile(path, newData, 0644)
}

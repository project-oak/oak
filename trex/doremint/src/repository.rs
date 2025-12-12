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

use std::{collections::HashMap, fs, path::Path, str::FromStr};

use anyhow::{Context, Result};
use oci_spec::image::Digest;
use sha2::{Digest as ShaDigest, Sha256};
use trex_client::{CASClient, Entry, Index};

/// Ensures that the necessary directory structure for an OCI-like repository
/// exists. Specifically, it creates the `blobs/sha256` subdirectory where
/// content-addressable blobs are stored.
///
/// `index.json` is also necessary for the repository, but not created here,
/// since it is created by [`repository_add_file`] if not already existing.
pub fn prepare_repository(repository_path: &Path) -> Result<()> {
    let blobs_dir = repository_path.join("blobs").join("sha256");
    fs::create_dir_all(&blobs_dir).context("Failed to create blobs directory")
}

/// Adds a file (represented by its content bytes) to the OCI-like repository.
///
/// This function performs the following steps:
/// 1. Ensures the repository's directory structure is in place using
///    `prepare_repository`.
/// 2. Computes the SHA256 digest of the content.
/// 3. Stores the content as a blob in the `blobs/sha256` directory, using its
///    hexadecimal digest as the filename. If the blob already exists, it is not
///    rewritten.
/// 4. Creates an `Entry` for the added blob, including provided annotations.
/// 5. Updates the `index.json` file in the repository root to include this new
///    entry.
///
/// # Arguments
/// * `repository_path` - The root path of the OCI-like repository.
/// * `content` - The bytes of the file to add.
/// * `annotations` - A HashMap of annotations to associate with the entry in
///   `index.json`.
///
/// # Returns
/// A `Result` containing the `Entry` of the added file on success, or an
/// `anyhow::Error` on failure.
pub fn repository_add_file(
    repository_path: &Path,
    content: &[u8],
    annotations: HashMap<String, Vec<String>>,
) -> Result<Entry> {
    prepare_repository(repository_path)?;

    // 2. Hash content to create a content-addressable identifier.
    let hash = Sha256::digest(content);
    let digest_hex = hex::encode(hash);
    let digest_str = format!("sha256:{}", digest_hex);

    // 3. Stash the content as a blob in the `blobs/sha256` directory.
    let blobs_dir = repository_path.join("blobs").join("sha256");
    let blob_path = blobs_dir.join(&digest_hex);
    if !blob_path.exists() {
        fs::write(&blob_path, content).context("Failed to stash blob")?;
        eprintln!("Stashed blob to {:?}", blob_path);
    } else {
        eprintln!("Blob already exists at {:?}", blob_path);
    }

    // 4. Create an Entry for the new blob.
    let digest = Digest::from_str(&digest_str).context("Failed to parse digest")?;

    let entry = Entry { digest, annotations: annotations.clone() };

    // 5. Update the repository's `index.json` to reference the new entry.
    let index_path = repository_path.join("index.json");
    update_index(&index_path, vec![entry.clone()])?;

    Ok(entry)
}

/// Updates an index file (`index.json`) with new or updated entries.
///
/// If the `index.json` file does not exist, a new one is created.
/// Existing entries in the index with the same digest as a
/// `new_entry` are replaced.
///
/// # Arguments
/// * `path` - The path to the `index.json` file.
/// * `new_entries` - A vector of `Entry`s to add or update in the index.
///
/// # Returns
/// A `Result` indicating success or an `anyhow::Error` on failure.
fn update_index(path: &Path, new_entries: Vec<Entry>) -> Result<()> {
    // Load existing index or create a new one if it doesn't exist.
    let mut index = if path.exists() {
        let data = fs::read(path).context("Failed to read index")?;
        serde_json::from_slice(&data).context("Failed to parse existing index")?
    } else {
        Index { entries: vec![], cas_clients: vec![] }
    };

    if index.cas_clients.is_empty() {
        index.cas_clients.push(CASClient::OCI { url: "./blobs".to_string() });
    }

    for entry in new_entries {
        // Remove any existing entry with the same digest to ensure idempotence and
        // update capability.
        index.entries.retain(|e| e.digest != entry.digest);
        index.entries.push(entry);
    }

    // Serialize the updated index and write it back to the file.
    let new_data = serde_json::to_string_pretty(&index).context("Failed to marshal index")?;
    fs::write(path, new_data).context("Failed to write index")?;

    Ok(())
}

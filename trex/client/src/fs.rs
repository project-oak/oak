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

//! Filesystem-based implementations of EndorsementIndex and BlobFetcher.
//!
//! These implementations read from and write to a repository layout:
//! ```text
//! repository/
//! ├── blobs/
//! │   └── <typed_hash>   # content-addressable blobs (e.g. sha256:abcd...)
//! └── <index_name>/
//!     └── <typed_hash>   # newline-separated list of value digests
//! ```

use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
};

use anyhow::{Context, Result};
use async_trait::async_trait;
use oak_digest::Digest;

use crate::{
    BlobFetcher, BlobWriter, EndorsementIndex, EndorsementIndexWriter, STATEMENT_TO_BUNDLE_INDEX,
    SUBJECT_TO_STATEMENT_INDEX,
};

/// Filesystem-based endorsement index for read and write operations.
pub struct FileSystemEndorsementIndex {
    repository_path: PathBuf,
}

impl FileSystemEndorsementIndex {
    /// Creates a new filesystem index at the given repository path.
    pub fn new(repository_path: PathBuf) -> Self {
        Self { repository_path }
    }

    /// Ensures the repository directory structure exists.
    pub fn prepare(&self) -> Result<()> {
        let blobs_dir = self.repository_path.join("blobs");
        fs::create_dir_all(&blobs_dir).context("Failed to create blobs directory")
    }

    fn fetch_digests(&self, index_name: &str, key_digest: &Digest) -> Result<Vec<Digest>> {
        let index_file_path =
            self.repository_path.join(index_name).join(key_digest.to_typed_hash());

        if !index_file_path.exists() {
            return Ok(Vec::new());
        }

        let body = fs::read_to_string(&index_file_path).context("reading index file")?;
        let digests = crate::parse_index(&body)?;
        Ok(digests)
    }

    fn add_index_entry(
        &self,
        index_name: &str,
        key_digest: &Digest,
        value_digest: &Digest,
    ) -> Result<()> {
        let key_typed = key_digest.to_typed_hash();
        let value_typed = value_digest.to_typed_hash();
        let index_dir = self.repository_path.join(index_name);
        fs::create_dir_all(&index_dir).context("Failed to create index directory")?;

        let index_file_path = index_dir.join(&key_typed);

        // Check if the entry already exists to avoid duplicates.
        let content = fs::read_to_string(&index_file_path).unwrap_or_default();
        if content.lines().any(|line| line.trim() == value_typed) {
            log::debug!(
                "Entry {} -> {} already exists in index {}",
                key_typed,
                value_typed,
                index_name
            );
            return Ok(());
        }

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&index_file_path)
            .context("Failed to open index file")?;

        writeln!(file, "{}", value_typed).context("Failed to write to index file")?;
        log::debug!("Added entry {} -> {} in index {}", key_typed, value_typed, index_name);

        Ok(())
    }
}

#[async_trait]
impl EndorsementIndex for FileSystemEndorsementIndex {
    async fn lookup_endorsements(&self, subject_digest: &Digest) -> Result<Vec<Digest>> {
        self.fetch_digests(SUBJECT_TO_STATEMENT_INDEX, subject_digest)
    }

    async fn lookup_rekor_signatures(&self, endorsement_digest: &Digest) -> Result<Vec<Digest>> {
        self.fetch_digests(STATEMENT_TO_BUNDLE_INDEX, endorsement_digest)
    }
}

#[async_trait]
impl EndorsementIndexWriter for FileSystemEndorsementIndex {
    async fn add_subject_to_statement(&self, subject: &Digest, statement: &Digest) -> Result<()> {
        self.add_index_entry(SUBJECT_TO_STATEMENT_INDEX, subject, statement)
    }

    async fn add_statement_to_bundle(&self, statement: &Digest, bundle: &Digest) -> Result<()> {
        self.add_index_entry(STATEMENT_TO_BUNDLE_INDEX, statement, bundle)
    }
}

/// Filesystem-based blob store for read and write operations.
pub struct FileSystemBlobStore {
    repository_path: PathBuf,
}

impl FileSystemBlobStore {
    /// Creates a new filesystem blob store at the given repository path.
    pub fn new(repository_path: PathBuf) -> Self {
        Self { repository_path }
    }

    fn blob_path(&self, digest: &Digest) -> PathBuf {
        self.repository_path.join("blobs").join(digest.to_typed_hash())
    }

    /// Ensures the blobs directory structure exists.
    pub fn prepare(&self) -> Result<()> {
        let blobs_dir = self.repository_path.join("blobs");
        fs::create_dir_all(&blobs_dir).context("Failed to create blobs directory")
    }
}

#[async_trait]
impl BlobFetcher for FileSystemBlobStore {
    async fn fetch_blob(&self, digest: &Digest) -> Result<Vec<u8>> {
        let blob_path = self.blob_path(digest);
        let bytes =
            fs::read(&blob_path).with_context(|| format!("reading blob from {:?}", blob_path))?;

        // Verify digest.
        let actual = Digest::Sha256(oak_digest::Sha256::from_contents(&bytes));
        anyhow::ensure!(
            actual == *digest,
            "blob digest mismatch: expected {}, got {}",
            digest.to_typed_hash(),
            actual.to_typed_hash()
        );

        Ok(bytes)
    }
}

#[async_trait]
impl BlobWriter for FileSystemBlobStore {
    async fn store_blob(&self, content: &[u8]) -> Result<Digest> {
        self.prepare()?;

        let digest = Digest::Sha256(oak_digest::Sha256::from_contents(content));
        let blob_path = self.blob_path(&digest);

        if !blob_path.exists() {
            fs::write(&blob_path, content)
                .with_context(|| format!("writing blob to {:?}", blob_path))?;
            log::debug!("Stored blob to {:?}", blob_path);
        } else {
            log::debug!("Blob already exists at {:?}", blob_path);
        }

        Ok(digest)
    }
}

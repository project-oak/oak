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

//! HTTP-based implementations of [`EndorsementIndex`] and [`BlobFetcher`].
//!
//! These implementations fetch endorsement data from a remote OCI-like
//! repository served over HTTP. The expected URL layout mirrors the filesystem
//! layout described in the [`fs`](super::fs) module:
//!
//! ```text
//! <base_url>/
//! ├── blobs/<typed_hash>        # content-addressable blobs
//! └── <index_name>/<typed_hash>  # newline-separated value digests
//! ```

use anyhow::{Context, Result};
use async_trait::async_trait;
use oak_digest::Digest;

use crate::{BlobFetcher, EndorsementIndex, STATEMENT_TO_BUNDLE_INDEX, SUBJECT_TO_STATEMENT_INDEX};

/// HTTP-based endorsement index backed by a remote OCI-like repository.
///
/// An `HttpEndorsementIndex` reads index entries by issuing HTTP `GET` requests
/// to `{base_url}/{index_name}/{typed_hash}`. A `404 Not Found` response is
/// treated as an empty result set rather than an error.
pub struct HttpEndorsementIndex {
    base_url: String,
}

impl HttpEndorsementIndex {
    pub fn new(base_url: String) -> Self {
        Self { base_url }
    }

    async fn fetch_digests(&self, index_name: &str, key_digest: &Digest) -> Result<Vec<Digest>> {
        let url = format!(
            "{}/{}/{}",
            self.base_url.trim_end_matches('/'),
            index_name,
            key_digest.to_typed_hash()
        );
        log::debug!("Fetching index entries from: {url}");
        let resp = reqwest::get(&url).await.context("fetching index entry")?;

        if resp.status() == reqwest::StatusCode::NOT_FOUND {
            return Ok(Vec::new());
        }

        if !resp.status().is_success() {
            log::error!("Failed to fetch index from {url}: {}", resp.status());
            anyhow::bail!("failed to fetch index from {url}: {}", resp.status());
        }

        let body = resp.text().await.context("reading index body")?;
        let digests = crate::parse_index(&body)?;
        Ok(digests)
    }
}

#[async_trait]
impl EndorsementIndex for HttpEndorsementIndex {
    async fn lookup_endorsements(&self, subject_digest: &Digest) -> Result<Vec<Digest>> {
        self.fetch_digests(SUBJECT_TO_STATEMENT_INDEX, subject_digest).await
    }

    async fn lookup_rekor_signatures(&self, endorsement_digest: &Digest) -> Result<Vec<Digest>> {
        self.fetch_digests(STATEMENT_TO_BUNDLE_INDEX, endorsement_digest).await
    }
}

/// HTTP-based blob fetcher backed by a remote OCI-like repository.
///
/// Fetches blobs from `{base_url}/blobs/{typed_hash}` and verifies that the
/// returned content matches the requested digest.
pub struct HttpBlobFetcher {
    base_url: String,
}

impl HttpBlobFetcher {
    /// Construct an instance of `HttpBlobFetcher` with the provided HTTP
    /// base URL.
    pub fn new(base_url: String) -> Self {
        Self { base_url }
    }
}

#[async_trait]
impl BlobFetcher for HttpBlobFetcher {
    async fn fetch_blob(&self, digest: &Digest) -> Result<Vec<u8>> {
        let url =
            format!("{}/blobs/{}", self.base_url.trim_end_matches('/'), digest.to_typed_hash());
        log::debug!("Fetching blob from: {url}");
        let resp = reqwest::get(&url).await.context("fetching blob")?;

        if !resp.status().is_success() {
            log::error!("Failed to fetch blob from {}: {}", url, resp.status());
            anyhow::bail!("failed to fetch blob from {}: {}", url, resp.status());
        }

        let bytes = resp.bytes().await.context("reading blob body")?;

        // Verify digest.
        let actual = Digest::Sha256(oak_digest::Sha256::from_contents(&bytes));
        anyhow::ensure!(
            actual == *digest,
            "blob digest mismatch: expected {}, got {}",
            digest.to_typed_hash(),
            actual.to_typed_hash()
        );

        Ok(bytes.to_vec())
    }
}

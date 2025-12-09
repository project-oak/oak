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

use anyhow::{Context, Result};
use async_trait::async_trait;
use digest_util::{hex_digest_from_contents, hex_digest_from_typed_hash, is_hex_digest_match};
use oak_proto_rust::oak::HexDigest;
use oci_spec::image::ImageIndex;

use crate::{BlobFetcher, EndorsementIndex};

pub async fn fetch_index(prefix: &str) -> Result<ImageIndex> {
    let url = format!("{}/index.json", prefix.trim_end_matches('/'));
    log::info!("Fetching index from: {url}");
    let resp = reqwest::get(&url).await.context("fetching index.json")?;

    if !resp.status().is_success() {
        log::error!("Failed to fetch index from {url}: {}", resp.status());
        anyhow::bail!("failed to fetch index from {url}: {}", resp.status());
    }

    let body = resp.bytes().await.context("reading index body")?;
    let index: ImageIndex = serde_json::from_slice(&body).context("parsing index.json")?;

    Ok(index)
}

pub struct HttpEndorsementIndex {
    index_getter: Box<dyn Fn() -> ImageIndex + Send + Sync>,
}

impl HttpEndorsementIndex {
    pub fn new(index_getter: Box<dyn Fn() -> ImageIndex + Send + Sync>) -> Self {
        Self { index_getter }
    }
}

#[async_trait]
impl EndorsementIndex for HttpEndorsementIndex {
    async fn lookup_oak_tr_endorsements(
        &self,
        subject_digest: &HexDigest,
    ) -> Result<Vec<HexDigest>> {
        let subject_digest_str = format!("sha256:{}", subject_digest.sha2_256);
        log::debug!("Looking up Oak TR endorsements for subject: {subject_digest_str}");
        let digests: Vec<HexDigest> = (self.index_getter)()
            .clone()
            .manifests()
            .iter()
            .filter(|entry| crate::is_oak_endorsement(entry, &subject_digest_str))
            .filter_map(|entry| hex_digest_from_typed_hash(entry.digest().as_ref()).ok())
            .collect();
        Ok(digests)
    }

    async fn lookup_rekor_signatures(
        &self,
        endorsement_digest: &HexDigest,
    ) -> Result<Vec<HexDigest>> {
        let endorsement_digest_str = format!("sha256:{}", endorsement_digest.sha2_256);
        log::debug!("Looking up Rekor signatures for Oak TR endorsement: {endorsement_digest_str}");
        let digests: Vec<HexDigest> = (self.index_getter)()
            .manifests()
            .iter()
            .filter(|entry| crate::is_hashed_rekord(entry, &endorsement_digest_str))
            .filter_map(|entry| hex_digest_from_typed_hash(entry.digest().as_ref()).ok())
            .collect();
        log::info!(
            "Found {} Rekor signatures for Oak TR endorsement {endorsement_digest_str}",
            digests.len()
        );
        Ok(digests)
    }
}

pub struct HttpBlobFetcher {
    prefix: String,
}

impl HttpBlobFetcher {
    /// Construct an instance of `HttpBlobFetcher` with the provided HTTP
    /// prefix.
    ///
    /// Example value for `prefix`: `https://raw.githubusercontent.com/tiziano88/endorsements/refs/heads/main`.
    pub fn new(prefix: String) -> Self {
        Self { prefix: prefix.trim_end_matches('/').to_string() }
    }
}

#[async_trait]
impl BlobFetcher for HttpBlobFetcher {
    async fn fetch_blob(&self, digest: &HexDigest) -> Result<Vec<u8>> {
        // Construct URL: prefix/blobs/sha256/<hex>
        // Assuming sha256 for now.
        if digest.sha2_256.is_empty() {
            anyhow::bail!("only sha256 supported for fetching blobs");
        }

        let url = format!("{}/blobs/sha256/{}", self.prefix, digest.sha2_256);
        log::debug!("Fetching blob from: {url}");
        let resp = reqwest::get(&url).await.context("fetching blob")?;

        if !resp.status().is_success() {
            log::error!("Failed to fetch blob from {}: {}", url, resp.status());
            anyhow::bail!("failed to fetch blob from {}: {}", url, resp.status());
        }

        let bytes = resp.bytes().await.context("reading blob body")?;

        // Verify digest.
        let actual_digest = hex_digest_from_contents(&bytes);
        is_hex_digest_match(&actual_digest, digest).context("verifying blob digest")?;

        Ok(bytes.to_vec())
    }
}

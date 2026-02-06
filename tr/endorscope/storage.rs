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

//! This module defines loaders that provide methods for loading endorsement
//! packages from various sources.
//!
//! - [`EndorsementLoader`]: loads endorsement and reference values from a
//!   remote content addressable storage layer provided by the trait
//!   [`ContentAddressable`].
//! - [`CaStorage`]: A concrete implementation of [`ContentAddressable`] which
//!   is based on the HTTP protocol.
//!
//! First create a loader:
//!
//! let storage = CaStorage { url_prefix, fbucket, ibucket };
//! let loader = EndorsementLoader::new(Box::new(storage));
//!
//! Then use it e.g. to load and verify the most recent endorsement package
//! signed by a particular verifying key:
//!
//! let hashes = loader.list_endorsements_by_key(key_hash)?;
//! let package = loader.load(hashes[hashes.len() - 1], rekor_public_key)?;
//! package.verify(now).context("verifying endorsement")?;

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};

use anyhow::{Context, Result};
use intoto::statement::{get_hex_digest_from_statement, parse_statement};
use oak_digest::Sha256;
use url::Url;

use crate::package::Package;

const INLINE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/77149.md";
const MPM_CLAIM_TYPE: &str = "https://github.com/project-oak/oak/blob/main/docs/tr/claim/31543.md";

// Link types establish certain relationships between items in the
// content-addressable storage, similar to database indices. Details can be
// found at go/oak-search-index-structure.
const ENDORSEMENT_FOR_SUBJECT_LINK: &str = "13";
const SIGNATURE_FOR_ENDORSEMENT_LINK: &str = "14";
const LOG_ENTRY_FOR_ENDORSEMENT_LINK: &str = "15";
const PUBLIC_KEY_FOR_SIGNATURE_LINK: &str = "16";
const ENDORSEMENTS_FOR_KEY_LINK: &str = "21";
const KEYS_FOR_KEYSET_LINK: &str = "22";
const ENDORSEMENTS_FOR_CLAIM_LINK: &str = "36";

/// ContentAddressable is a trait that defines the interface for a
/// content-addressable storage layer.
///
/// The interface defines methods for getting files and links from the storage
/// layer. The files are identified by their content hash, which usually is
/// the SHA2-256 hash of the file's contents.
///
/// The links are identified by their link type and the hash of the file they
/// link from. A link type is any of the *_LINK constants, it's roughly a
/// database search index that models a certain semantic relationship between
/// hashes.
///
/// See go/oak-search-index-structure for context and a description of all
/// existing link types.
pub trait ContentAddressable {
    /// Returns the contents of the file in `fbucket` with the given hash.
    ///
    /// Params:
    /// - content_hash: the hash of the file to get the contents for.
    ///
    /// Returns:
    /// - The contents of the file.
    fn get_file(&self, content_hash: &str) -> Result<Vec<u8>>;

    /// Returns the hash of a linked file with the given link type.
    ///
    /// Params:
    /// - content_hash: the hash of the file to get the linked file for.
    /// - link_type: the link type of the linked file.
    ///
    /// Returns:
    /// - The hash of the linked file.
    fn get_link(&self, content_hash: &str, link_type: &str) -> Result<String>;

    /// Returns the contents of a linked file with the given link type.
    ///
    /// Params:
    /// - content_hash: the hash of the file to get the linked file for.
    /// - link_type: the link type of the linked file.
    ///
    /// Returns:
    /// - The contents of the linked file.
    fn get_linked_file(&self, content_hash: &str, link_type: &str) -> Result<Vec<u8>>;
}

/// Loads endorsement package from a content-addressable storage layer.
///
/// The details of the storage layer are defined by the trait
/// [`ContentAddressable`], so one can define a number of storage layers.
pub struct EndorsementLoader {
    storage: Box<dyn ContentAddressable>,
}

impl EndorsementLoader {
    /// Creates a new remote endorsement loader.
    ///
    /// Params:
    /// - storage: the content-addressable storage layer to load from.
    pub fn new(storage: Box<dyn ContentAddressable>) -> Self {
        EndorsementLoader { storage }
    }

    /// Lists all endorser keys for the given endorser keyset hash.
    ///
    /// Returns:
    /// - The list of endorser key hashes.
    pub fn list_keys_by_keyset(&self, endorser_keyset_hash: &str) -> Result<Vec<String>> {
        let endorser_keys = self
            .storage
            .get_link(endorser_keyset_hash, KEYS_FOR_KEYSET_LINK)
            .with_context(|| format!("reading endorser keys for keyset {}", endorser_keyset_hash))
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorser keyset is not found in
                // the index, we treat it as if the endorser keyset is empty.
                // So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;
        Ok(endorser_keys.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    /// Lists all endorsement hashes for the given endorser key hash.
    ///
    /// The endorsement hashes are sorted by date of issuance (`issuedOn`)
    /// such that the most recent endorsement comes last.
    ///
    /// Returns:
    /// - The list of endorsement hashes.
    pub fn list_endorsements_by_key(&self, endorser_key_hash: &str) -> Result<Vec<String>> {
        let endorsements = self
            .storage
            .get_link(endorser_key_hash, ENDORSEMENTS_FOR_KEY_LINK)
            .with_context(|| format!("reading endorsements by key {}", endorser_key_hash))
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorsement list is not found
                // in the index, we assume the endorser has not signed any
                // endorsements. So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;

        Ok(endorsements.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    /// Lists all endorsement hashes for the given subject hash.
    ///
    /// The endorsement hashes are sorted by date of issuance (`issuedOn`)
    /// such that the most recent endorsement comes last.
    ///
    /// Returns:
    /// - The list of endorsement hashes.
    pub fn list_endorsements_by_subject(&self, subject_hash: &str) -> Result<Vec<String>> {
        let endorsements = self
            .storage
            .get_link(subject_hash, ENDORSEMENT_FOR_SUBJECT_LINK)
            .with_context(|| format!("reading endorsements by subject {}", subject_hash))
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorsement list is not found in
                // the index, we assume the subject has never been endorsed.
                // So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;

        Ok(endorsements.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    /// Lists all endorsement hashes for the given claim.
    ///
    /// The endorsement hashes are sorted by date of issuance (`issuedOn`)
    /// such that the most recent endorsement comes last.
    ///
    /// Returns:
    /// - The list of endorsement hashes.
    pub fn list_endorsements_by_claim(&self, claim_type: &str) -> Result<Vec<String>> {
        let claim_hash = Sha256::from_contents(claim_type.as_bytes());
        let endorsements = self
            .storage
            .get_link(&claim_hash.to_typed_hash(), ENDORSEMENTS_FOR_CLAIM_LINK)
            .with_context(|| format!("reading endorsements by claim {}", claim_type))
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorsement list is not found in
                // the index, we assume the subject has never been endorsed.
                // So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;

        Ok(endorsements.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    /// Loads an endorsement package from remote content-addressable storage.
    ///
    /// Params:
    /// - endorsement_hash: The hash of the endorsement which identifies the
    ///   endorsement package.
    /// - rekor_public_key: Rekor's verifying key if a log entry is expected and
    ///   should be verified. If it is not expected, pass `None`.
    ///
    /// Returns:
    /// - The endorsement package.
    pub fn load(
        &self,
        endorsement_hash: &str,
        rekor_public_key: Option<String>,
    ) -> Result<Package> {
        let endorsement = self
            .storage
            .get_file(endorsement_hash)
            .with_context(|| format!("reading endorsement for endorsement {}", endorsement_hash))?;
        let signature = self
            .storage
            .get_linked_file(endorsement_hash, SIGNATURE_FOR_ENDORSEMENT_LINK)
            .with_context(|| {
                format!("reading signature file for endorsement {}", endorsement_hash)
            })?;
        let log_entry = self
            .storage
            .get_linked_file(endorsement_hash, LOG_ENTRY_FOR_ENDORSEMENT_LINK)
            .with_context(|| {
                format!("reading rekor log entry for endorsement {}", endorsement_hash)
            })
            .map(Some)
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the rekor log entry is not found in the
                // index, we assume the endorsement is not committed to a
                // transparency log.
                Some(ureq::Error::Status(404, _)) => Ok(None),
                _ => Err(err),
            })?;

        let statement = parse_statement(&endorsement).context("parsing endorsement statement")?;
        let mut subject: Option<Vec<u8>> = None;
        if statement
            .predicate
            .claims
            .iter()
            .any(|c| c.r#type == INLINE_CLAIM_TYPE || c.r#type == MPM_CLAIM_TYPE)
        {
            let hex_digest = get_hex_digest_from_statement(&statement)?;
            subject = Some(self.storage.get_file(&format!("sha2-256:{}", &hex_digest.sha2_256))?);
        }

        let signature_hash =
            self.storage.get_link(endorsement_hash, SIGNATURE_FOR_ENDORSEMENT_LINK).with_context(
                || format!("reading signature link for endorsement {}", endorsement_hash),
            )?;
        let endorser_public_key = self
            .storage
            .get_linked_file(signature_hash.as_str(), PUBLIC_KEY_FOR_SIGNATURE_LINK)
            .with_context(|| {
                format!("reading endorser public key for endorsement {}", endorsement_hash)
            })
            .and_then(|pem| String::from_utf8(pem).context("parsing endorser public key"))?;

        Ok(Package {
            endorsement,
            signature,
            log_entry,
            subject,
            endorser_public_key,
            rekor_public_key,
        })
    }
}

/// Implements the [`ContentAddressable`] trait which is based on the
/// HTTP protocol.
pub struct CaStorage {
    /// The prefix of the URL to the content-addressable storage.
    pub url_prefix: Url,

    /// The name of the file bucket.
    pub fbucket: String,

    /// The name of the index bucket.
    pub ibucket: String,
}

impl ContentAddressable for CaStorage {
    fn get_file(&self, file_hash: &str) -> Result<Vec<u8>> {
        let suffix = format!("{}/{}", self.fbucket, file_hash);
        let url = self.url_prefix.join(&suffix)?;
        fetch(&url)
    }

    fn get_linked_file(&self, file_hash: &str, link_type: &str) -> Result<Vec<u8>> {
        let link_file_hash = self.get_link(file_hash, link_type)?;
        self.get_file(&link_file_hash).with_context(|| {
            format!("reading link file {link_type} ({link_file_hash}) for file {file_hash}")
        })
    }

    fn get_link(&self, file_hash: &str, link_type: &str) -> Result<String> {
        let suffix = format!("{}/{}/{}", self.ibucket, link_type, file_hash);
        let url = self.url_prefix.join(&suffix)?;
        let fetch_result = fetch(&url)?;
        fetch_result
            .try_into()
            .with_context(|| format!("parsing link {link_type} for file {file_hash}"))
    }
}

// Fetches the content of the given URL.
// This probably should be a mockable trait of some kind to help with testing.
fn fetch(url: &Url) -> Result<Vec<u8>> {
    let response = ureq::get(url.as_ref()).call().with_context(|| format!("fetching URL {url}"))?;
    let mut buffer = Vec::new();
    response
        .into_reader()
        .read_to_end(&mut buffer)
        .with_context(|| format!("reading response bytes from URL {url}"))?;
    Ok(buffer)
}

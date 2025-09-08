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

//! This module defines the a number of endorsement loaders that provide methods
//! for loading endorsement and reference values from different sources.
//!
//! - [`FileEndorsementLoader`]: loads endorsement and reference values from
//!   local files.
//! - [`ContentAddressableEndorsementLoader`]: loads endorsement and reference
//!   values from a remote content addressable storage layer provided by the
//!   trait [`ContentAddressableStorage`].
//!
//! The module also defines an implementation of the
//! [`ContentAddressableStorage`] trait based on the HTTP protocol.

use std::{fs, path::PathBuf, sync::Arc};

use anyhow::{Context, Result};
use derive_builder::Builder;
use intoto::statement::{get_digest, parse_statement};
use oak_attestation_verification::convert_pem_to_raw;
use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{
    endorsement::Format, verifying_key_reference_value, ClaimReferenceValue, Endorsement,
    EndorsementReferenceValue, KeyType, Signature, SignedEndorsement, VerifyingKey,
    VerifyingKeyReferenceValue, VerifyingKeySet,
};
use url::Url;

use crate::list::MPM_CLAIM_TYPE;

// The key ID for the endorser key is used because the reference values could
// contain multiple keys. However, is meaningless in this setting, as we are
// fetching a single set of reference values. We just make sure we use the same
// number in signed endorsement and reference values.
const KEY_ID: u32 = 1;

const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

// FileEndorsement is a struct that contains the paths to the files needed to
// load and verify an endorsement.
#[derive(Builder)]
pub(crate) struct FileEndorsement {
    // The path to the endorsement.json to verify.
    endorsement_path: PathBuf,
    // The path to the signature of the endorsement.
    signature_path: PathBuf,
    // The path to the public key of the endorser, which produced the endorsement and signature.
    endorser_public_key_path: PathBuf,
    // If the endorsement signature has been committed to a transparency log,
    // the path to the log entry.
    log_entry_path: Option<PathBuf>,
    // If the subject of the endorsement was inlined inside the endorsement,
    // the path to the subject.
    subject_path: Option<PathBuf>,
}

// FileEndorsementLoader is a struct that loads endorsement and reference
// values from local files.
pub(crate) struct FileEndorsementLoader {}

impl FileEndorsementLoader {
    // Loads an endorsement and its reference values.
    pub fn load_endorsement(
        &self,
        params: FileEndorsement,
    ) -> Result<(SignedEndorsement, EndorsementReferenceValue)> {
        let signed_endorsement = self.load_signed_endorsement(&params)?;
        let reference_values = self.load_reference_values(&params)?;
        Ok((signed_endorsement, reference_values))
    }

    fn load_signed_endorsement(&self, params: &FileEndorsement) -> Result<SignedEndorsement> {
        let endorsement = fs::read(&params.endorsement_path).with_context(|| {
            format!("reading endorsement from {}", &params.endorsement_path.display())
        })?;
        let signature = fs::read(&params.signature_path).with_context(|| {
            format!("reading signature from {}", &params.signature_path.display())
        })?;
        let log_entry = match &params.log_entry_path {
            None => Vec::new(),
            Some(path) => fs::read(path)
                .with_context(|| format!("reading log_entry from {}", path.display()))?,
        };
        let subject = match &params.subject_path {
            None => Vec::new(),
            Some(path) => {
                fs::read(path).context(format!("reading subject from {}", path.display()))?
            }
        };
        let signed_endorsement = SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: endorsement,
                subject,
            }),
            // This endorsement will be validated agains the key we will construct in
            // load_reference_values. So we make sure they share the same key ID.
            signature: Some(Signature { key_id: KEY_ID, raw: signature.to_vec() }),
            rekor_log_entry: log_entry,
        };
        Ok(signed_endorsement)
    }

    fn load_reference_values(&self, params: &FileEndorsement) -> Result<EndorsementReferenceValue> {
        let endorser_key = fs::read_to_string(&params.endorser_public_key_path)
            .with_context(|| {
                format!(
                    "reading endorser public key from {}",
                    params.endorser_public_key_path.display()
                )
            })
            .and_then(|pem| convert_pem_to_raw(pem.as_str()))
            .map(|raw| VerifyingKey {
                r#type: KeyType::EcdsaP256Sha256.into(),
                // The key will be used to validate the endorsement signature. So we make sure
                // the key ID is the same in signed endorsement and reference values.
                key_id: KEY_ID,
                raw,
            })?;

        let rekor_key = VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: KEY_ID,
            raw: get_rekor_public_key_raw(),
        };

        let ref_value = EndorsementReferenceValue {
            endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
            required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
            rekor: Some(VerifyingKeyReferenceValue {
                r#type: Some(verifying_key_reference_value::Type::Verify(VerifyingKeySet {
                    keys: [rekor_key].to_vec(),
                    ..Default::default()
                })),
            }),
            ..Default::default()
        };

        Ok(ref_value)
    }
}

// ContentAddressableStorage is a trait that defines the interface for a
// content addressable storage layer.
//
// The interface defines methods for getting files and links from the storage
// layer. The files are identified by their content hash, which is the SHA256
// hash of the file's content. The links are identified by their link type and
// the hash of the file they link from.
//
// See go/oak-search-index-structure for details on the definition of this
// structure.
pub(crate) trait ContentAddressableStorage {
    // Returns the content of the file in fbucket_name with the given.
    fn get_file(&self, content_hash: &str) -> Result<Vec<u8>>;

    // Returns the file hash of a linked file with the given link type.
    fn get_link(&self, content_hash: &str, link_type: &str) -> Result<String>;

    // Returns the content of a linked file with the given link type.
    //
    // Params:
    // - content_hash: the hash of the file to get the linked file for.
    // - link_type: the link type of the linked file.
    //
    // Returns:
    // - The content of the linked file.
    fn get_linked_file(&self, content_hash: &str, link_type: &str) -> Result<Vec<u8>>;
}

// ContentAddressableEndorsementLoader is a struct that loads endorsement and
// reference values from a content addressable storage layer.
//
// The details of the storage layer are defined by the trait
// [`ContentAddressableStorage`], so one can define a number of storage layers.
pub(crate) struct ContentAddressableEndorsementLoader {
    storage: Arc<dyn ContentAddressableStorage>,
}

// These are the link types used to organize the content addressable storage.
//
// See go/oak-search-index-structure for details on the definition of this
// structure.
const SIGNATURE_LINK: &str = "14";
const REKOR_LOG_ENTRY_LINK: &str = "15";
const PUBLIC_KEY_LINK: &str = "16";
const ENDORSEMENT_LIST_LINK: &str = "21";
const ENDORSER_KEYS_LIST_LINK: &str = "22";

impl ContentAddressableEndorsementLoader {
    // Creates a new remote endorsement loader.
    //
    // Params:
    // - storage: the content addressable storage layer to load from.
    pub(crate) fn new_with_storage(storage: Arc<dyn ContentAddressableStorage>) -> Self {
        ContentAddressableEndorsementLoader { storage }
    }

    // Lists all endorser keys for the given endorser keyset hash.
    //
    // Returns:
    // - The list of endorser keys.
    pub(crate) fn list_endorser_keys(&self, endorser_keyset_hash: &str) -> Result<Vec<String>> {
        let endorser_keys = self
            .storage
            .get_link(endorser_keyset_hash, ENDORSER_KEYS_LIST_LINK)
            .with_context(|| {
                format!("reading endorser keys list for endorser keyset {}", endorser_keyset_hash)
            })
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorser keyset is not found in the index, we treat it
                // as if the endorser keyset is empty. So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;
        Ok(endorser_keys.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    // Lists all endorsement hashes for the given endorser key hash.
    //
    // Returns:
    // - The list of endorsement hashes.
    pub(crate) fn list_endorsements(&self, endorser_key_hash: &str) -> Result<Vec<String>> {
        let endorsements = self
            .storage
            .get_link(endorser_key_hash, ENDORSEMENT_LIST_LINK)
            .with_context(|| format!("reading endorsement list for endorser {}", endorser_key_hash))
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the endorsement list is not found in the index, we assume
                // the endorser has not signed any endorsements. So we return an empty list.
                Some(ureq::Error::Status(404, _)) => Ok(String::new()),
                _ => Err(err),
            })?;

        Ok(endorsements.split_terminator("\n").map(|s| s.to_string()).collect())
    }

    // Loads endorsement and reference values from a remote content addressable
    // storage.
    //
    // Returns:
    // - The endorsement and reference values.
    pub(crate) fn load_endorsement(
        &self,
        endorsement_hash: &str,
    ) -> Result<(SignedEndorsement, EndorsementReferenceValue)> {
        let signed_endorsement = self.load_signed_endorsement(endorsement_hash)?;
        let reference_values = self.load_reference_values(endorsement_hash)?;
        Ok((signed_endorsement, reference_values))
    }

    fn load_signed_endorsement(&self, endorsement_hash: &str) -> Result<SignedEndorsement> {
        let endorsement = self
            .storage
            .get_file(endorsement_hash)
            .with_context(|| format!("reading endorsement for endorsement {}", endorsement_hash))?;

        let signature =
            self.storage.get_linked_file(endorsement_hash, SIGNATURE_LINK).with_context(|| {
                format!("reading signature file for endorsement {}", endorsement_hash)
            })?;

        let statement = parse_statement(&endorsement).context("parsing endorsement statement")?;
        let contains_mpm_claim =
            statement.predicate.claims.iter().any(|c| c.r#type == MPM_CLAIM_TYPE);
        let subject = if contains_mpm_claim {
            let hex_digest = get_digest(&statement)?;
            self.storage.get_file(&format!("sha2-256:{}", &hex_digest.sha2_256))?
        } else {
            vec![]
        };

        let rekor_log_entry = self
            .storage
            .get_linked_file(endorsement_hash, REKOR_LOG_ENTRY_LINK)
            .with_context(|| {
                format!("reading rekor log entry for endorsement {}", endorsement_hash)
            })
            .or_else(|err| match err.downcast_ref::<ureq::Error>() {
                // If the link file for the rekor log entry is not found in the
                // index, we assume the endorsement is not committed to a
                // transparency log.
                Some(ureq::Error::Status(404, _)) => Ok(vec![]),
                _ => Err(err),
            })?;

        let signed_endorsement = SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: endorsement,
                subject,
            }),
            signature: Some(Signature { key_id: KEY_ID, raw: signature }),
            rekor_log_entry,
        };
        Ok(signed_endorsement)
    }

    fn load_reference_values(&self, endorsement_hash: &str) -> Result<EndorsementReferenceValue> {
        let signature_hash =
            self.storage.get_link(endorsement_hash, SIGNATURE_LINK).with_context(|| {
                format!("reading signature link for endorsement {}", endorsement_hash)
            })?;

        let endorser_key = self
            .storage
            .get_linked_file(signature_hash.as_str(), PUBLIC_KEY_LINK)
            .with_context(|| {
                format!("reading endorser public key for endorsement {}", endorsement_hash)
            })
            .and_then(|pem| String::from_utf8(pem).context("parsing endorser public key"))
            .and_then(|pem| convert_pem_to_raw(pem.as_str()))
            .map(|raw| VerifyingKey {
                r#type: KeyType::EcdsaP256Sha256.into(),
                key_id: KEY_ID,
                raw,
            })?;

        let rekor_key = VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: KEY_ID,
            raw: get_rekor_public_key_raw(),
        };

        let ref_value = EndorsementReferenceValue {
            endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
            required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
            rekor: Some(VerifyingKeyReferenceValue {
                r#type: Some(verifying_key_reference_value::Type::Verify(VerifyingKeySet {
                    keys: [rekor_key].to_vec(),
                    ..Default::default()
                })),
            }),
            ..Default::default()
        };

        Ok(ref_value)
    }
}

// HTTPContentAddressableStorage is a struct that implements the
// ContentAddressableStorage trait based on the HTTP protocol.
#[derive(Builder)]
pub(crate) struct HTTPContentAddressableStorage {
    // The prefix of the URL to the content addressable storage.
    url_prefix: Url,
    // The name of the bucket containing the files.
    fbucket: String,
    // The name of the bucket containing the linked files.
    ibucket: String,
}

impl ContentAddressableStorage for HTTPContentAddressableStorage {
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

fn get_rekor_public_key_raw() -> Vec<u8> {
    let pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
        .expect("couldn't read Rekor public key");
    convert_pem_to_raw(&pem).expect("failed to convert Rekor key")
}

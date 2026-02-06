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

//! This module implements the `list` command. It lists all endorsements for a
//! given endorser key.

use anyhow::Context;
use clap::Args;
use endorscope::{
    package::Package,
    storage::{CaStorage, EndorsementLoader},
};
use intoto::statement::Validity;
use oak_proto_rust::oak::attestation::v1::MpmAttachment;
use oak_time::Instant;
use prost::Message;
use rekor::get_rekor_v1_public_key_pem;
use url::Url;
use verify_endorsement::verify_endorsement;

use crate::verify::{parse_bucket_name, parse_typed_hash, parse_url, string_to_option_string};

const MPM_CLAIM_TYPE: &str = "https://github.com/project-oak/oak/blob/main/docs/tr/claim/31543.md";
const FILE_IN_MPM_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/31544.md";
const MPM_VERSION_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/31545.md";
const CONFIGURATION_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/42362.md";
const PUBLISHED_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/52637.md";
const RUNNABLE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/68317.md";
const OPEN_SOURCE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/92939.md";
const PI_CLAIM_TYPE: &str = "https://github.com/project-oak/oak/blob/main/docs/tr/claim/39284.md";

const EXPECTED_CLAIMS: &[&str] =
    &[OPEN_SOURCE_CLAIM_TYPE, RUNNABLE_CLAIM_TYPE, PUBLISHED_CLAIM_TYPE, PI_CLAIM_TYPE];

fn prettify_claim(claim: &str) -> String {
    match claim {
        MPM_CLAIM_TYPE => format!("{claim} (Distributed as MPM)"),
        FILE_IN_MPM_CLAIM_TYPE => format!("{claim} (File in an MPM)"),
        CONFIGURATION_CLAIM_TYPE => format!("{claim} (Configuration)"),
        OPEN_SOURCE_CLAIM_TYPE => format!("{claim} (Open Source)"),
        RUNNABLE_CLAIM_TYPE => format!("{claim} (Runnable Binary)"),
        PUBLISHED_CLAIM_TYPE => format!("{claim} (Published Binary)"),
        PI_CLAIM_TYPE => format!("{claim} (Approved for Private AI Compute)"),
        _ => claim.to_string(),
    }
}

// Subcommand for listing all endorsements for a given endorser key.
//
// The fbucket_name and ibucket_name are used to determine the storage location
// of the content addressable files and the link index file. The url_prefix can
// be used to override the default storage location (Google Cloud Storage).
//
// Example:
//   list --endorser-key-hash=sha2-256:12345 --fbucket=12345 --ibucket=67890
#[derive(Args)]
pub(crate) struct ListArgs {
    #[command(flatten)]
    mode: ListMode,

    #[arg(
        long,
        help = "Public key to verify Rekor log entries, as PEM. Unset to disable verification, e.g. when log entries are not available by design.",
        default_value = get_rekor_v1_public_key_pem(),
    )]
    rekor_public_key: String,

    #[arg(
        long,
        help = "URL prefix of the content addressable storage.",
        default_value = "https://storage.googleapis.com",
        value_parser = parse_url,
    )]
    url_prefix: Url,

    #[arg(
        long,
        help = "Name of the file bucket associated with the index bucket.",
        value_parser = parse_bucket_name,
    )]
    fbucket: String,

    #[arg(
        long,
        help = "Name of the index GCS bucket.",
        value_parser = parse_bucket_name,
    )]
    ibucket: String,

    #[arg(long, help = "List at most that many items. No limit if zero.", default_value = "0")]
    limit: usize,
}

#[derive(Args)]
#[group(required = true, multiple = false)]
pub(crate) struct ListMode {
    #[arg(
        long,
        help = "Typed hash of the endorsed subject.",
        value_parser = parse_typed_hash,
    )]
    subject_hash: Option<String>,

    #[arg(
        long,
        help = "Typed hash of the verifying key used to sign endorsements.",
        value_parser = parse_typed_hash,
    )]
    endorser_key_hash: Option<String>,

    #[arg(
        long,
        help = "Typed hash of the endorser keyset used to sign endorsements.",
        value_parser = parse_typed_hash,
    )]
    endorser_keyset_hash: Option<String>,

    #[arg(long, help = "Lists all endorsements which contain the given claim.")]
    claim: Option<String>,
}

pub(crate) enum Mode {
    SubjectHash(String),
    EndorserKeyHash(String),
    EndorserKeysetHash(String),
    Claim(String),
}

impl ListMode {
    pub fn get(self) -> Mode {
        if let Some(hash) = self.subject_hash {
            Mode::SubjectHash(hash)
        } else if let Some(hash) = self.endorser_key_hash {
            Mode::EndorserKeyHash(hash)
        } else if let Some(hash) = self.endorser_keyset_hash {
            Mode::EndorserKeysetHash(hash)
        } else if let Some(claim_type) = self.claim {
            Mode::Claim(claim_type)
        } else {
            panic!("Exactly one mode must be specified");
        }
    }
}

/// Lists endorsements depending on arguments.
pub(crate) fn list(current_time: Instant, p: ListArgs) {
    let storage = CaStorage { url_prefix: p.url_prefix, fbucket: p.fbucket, ibucket: p.ibucket };
    let loader = EndorsementLoader::new(Box::new(storage));

    match p.mode.get() {
        Mode::SubjectHash(hash) => {
            list_endorsements_by_subject(
                current_time,
                &loader,
                hash.as_str(),
                string_to_option_string(p.rekor_public_key),
                p.limit,
            );
        }
        Mode::EndorserKeyHash(hash) => {
            list_endorsements_by_key(
                current_time,
                &loader,
                hash.as_str(),
                string_to_option_string(p.rekor_public_key),
                p.limit,
            );
        }
        Mode::EndorserKeysetHash(hash) => {
            let endorser_key_hashes = list_keys_by_keyset(&loader, hash.as_str());
            for endorser_key_hash in endorser_key_hashes {
                list_endorsements_by_key(
                    current_time,
                    &loader,
                    endorser_key_hash.as_str(),
                    string_to_option_string(p.rekor_public_key.clone()),
                    p.limit,
                );
            }
        }
        Mode::Claim(claim_type) => {
            list_endorsements_by_claim(
                current_time,
                &loader,
                claim_type.as_str(),
                string_to_option_string(p.rekor_public_key),
                p.limit,
            );
        }
    }
}

fn list_endorsement_hashes(
    current_time: Instant,
    loader: &EndorsementLoader,
    endorsement_hashes: Vec<String>,
    rekor_public_key: Option<String>,
    limit: usize,
) {
    // The index is append-only so we iterate backwards to show the most recent
    // endorsements first.
    for (index, endorsement_hash) in endorsement_hashes.iter().rev().enumerate() {
        let result = loader
            .load(endorsement_hash, rekor_public_key.clone())
            .with_context(|| format!("loading endorsement {endorsement_hash}"));
        match result {
            Ok(package) => verify_print_package(current_time, &package, endorsement_hash),
            Err(err) => println!("❌  Loading endorsement {} failed: {:?}", endorsement_hash, err),
        }
        if limit > 0 && index >= limit - 1 {
            break;
        }
    }
}

fn list_endorsements_by_subject(
    current_time: Instant,
    loader: &EndorsementLoader,
    subject_hash: &str,
    rekor_public_key: Option<String>,
    limit: usize,
) {
    let endorsement_hashes = loader.list_endorsements_by_subject(subject_hash);
    if endorsement_hashes.is_err() {
        println!("❌  Failed to list endorsements: {:?}", endorsement_hashes.err().unwrap());
        return;
    }

    list_endorsement_hashes(
        current_time,
        loader,
        endorsement_hashes.unwrap(),
        rekor_public_key,
        limit,
    );
}

fn list_keys_by_keyset(loader: &EndorsementLoader, endorser_keyset_hash: &str) -> Vec<String> {
    let endorser_keys = loader.list_keys_by_keyset(endorser_keyset_hash);
    if endorser_keys.is_err() {
        panic!("❌  Failed to list endorser keys: {:?}", endorser_keys.err().unwrap());
    }
    let endorser_keys = endorser_keys.unwrap();
    println!(
        "🧲  Found {} endorser keys for endorser keyset {}",
        endorser_keys.len(),
        endorser_keyset_hash
    );
    for endorser_key in &endorser_keys {
        println!("✅  {}", endorser_key);
    }
    endorser_keys
}

fn list_endorsements_by_key(
    current_time: Instant,
    loader: &EndorsementLoader,
    endorser_key_hash: &str,
    rekor_public_key: Option<String>,
    limit: usize,
) {
    let endorsement_hashes = loader.list_endorsements_by_key(endorser_key_hash);
    if endorsement_hashes.is_err() {
        println!("❌  Failed to list endorsements: {:?}", endorsement_hashes.err().unwrap());
        return;
    }
    let endorsement_hashes = endorsement_hashes.unwrap();

    println!(
        "🧲  Found {} endorsements for endorser key {}",
        endorsement_hashes.len(),
        endorser_key_hash
    );

    list_endorsement_hashes(current_time, loader, endorsement_hashes, rekor_public_key, limit);
}

fn list_endorsements_by_claim(
    current_time: Instant,
    loader: &EndorsementLoader,
    claim_type: &str,
    rekor_public_key: Option<String>,
    limit: usize,
) {
    let endorsement_hashes = loader.list_endorsements_by_claim(claim_type);
    if endorsement_hashes.is_err() {
        println!("❌  Failed to list endorsements: {:?}", endorsement_hashes.err().unwrap());
        return;
    }

    list_endorsement_hashes(
        current_time,
        loader,
        endorsement_hashes.unwrap(),
        rekor_public_key,
        limit,
    );
}

/// Verifies an endorsement package and pretty-prints it to stdout.
fn verify_print_package(current_time: Instant, package: &Package, endorsement_hash: &str) {
    let signed_endorsement =
        package.get_signed_endorsement().expect("failed to get signed endorsement");
    let result = verify_endorsement(
        current_time.into_unix_millis(),
        &signed_endorsement,
        &package.get_reference_value(),
    )
    .context("verifying endorsement");
    match result {
        Ok(statement) => {
            println!("    ✅  {endorsement_hash}");
            let details = statement.get_details().expect("failed to get endorsement details");
            match &details.subject_digest {
                Some(digest) => {
                    println!("        Subject:     sha2-256:{}", hex::encode(&digest.sha2_256));
                }
                None => {
                    println!("        Subject:     missing");
                }
            }
            match &details.valid {
                Some(v) => {
                    let vstruct = Validity::try_from(v).expect("failed to convert validity");
                    println!("        Not before:  {}", vstruct.not_before);
                    println!("        Not after:   {}", vstruct.not_after);
                }
                None => {
                    println!("        Validity:    missing");
                }
            }
            if details.claim_types.iter().any(|c| c.as_str() == MPM_CLAIM_TYPE) {
                let subject = &signed_endorsement.endorsement.as_ref().unwrap().subject;
                let mpm_attachment = MpmAttachment::decode(subject.as_slice()).unwrap();
                println!("        🍀  MPM version ID: {}", mpm_attachment.package_version);
            }
            for e in EXPECTED_CLAIMS {
                let claim = details.claim_types.iter().find(|c| c.as_str() == *e);
                if claim.is_none() {
                    println!("        ❌  {}", prettify_claim(e));
                } else {
                    println!("        🛄  {}", prettify_claim(e));
                }
            }
            for c in details.claim_types {
                if c.starts_with(MPM_VERSION_CLAIM_TYPE) {
                    let mpm_version_id =
                        c.strip_prefix(MPM_VERSION_CLAIM_TYPE).unwrap().strip_prefix("?").unwrap();
                    println!("        🛠  {}", mpm_version_id);
                } else if !EXPECTED_CLAIMS.contains(&c.as_str()) {
                    println!("        🛄  {}", prettify_claim(&c));
                }
            }
        }
        Err(err) => println!("    ❌  {endorsement_hash}: {:?}", err),
    }
}

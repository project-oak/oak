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

use std::sync::Arc;

use anyhow::Context;
use clap::Args;
use intoto::statement::Validity;
use oak_attestation_verification::verify_endorsement;
use oak_proto_rust::oak::attestation::v1::MpmAttachment;
use prost::Message;
use url::Url;

use crate::{
    endorsement_loader,
    verify::{parse_bucket_name, parse_typed_hash, parse_url},
};

// Subcommand for listing all endorsements for a given endorser key.
//
// The fbucket_name and ibucket_name are used to determine the storage location
// of the content addressable files and the link index file. The url_prefix can
// be used to override the default storage location (Google Cloud Storage).
//
// Example:
//   list --endorser_key_hash=sha2-256:12345 --fbucket=12345 --ibucket=67890
#[derive(Args)]
pub(crate) struct ListArgs {
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
}

// Lists all endorsements for a given endorser key.
pub(crate) fn list(p: ListArgs, now_utc_millis: i64) {
    let storage = endorsement_loader::HTTPContentAddressableStorageBuilder::default()
        .url_prefix(p.url_prefix)
        .fbucket(p.fbucket)
        .ibucket(p.ibucket)
        .build()
        .expect("Failed to build storage");

    let loader = endorsement_loader::ContentAddressableEndorsementLoader::new_with_storage(
        Arc::new(storage),
    );

    let endorser_key_hashes;
    if p.endorser_key_hash.is_some() {
        endorser_key_hashes = vec![p.endorser_key_hash.unwrap()];
    } else if p.endorser_keyset_hash.is_some() {
        endorser_key_hashes = list_endorser_keys(&loader, p.endorser_keyset_hash.unwrap().as_str());
    } else {
        panic!("Either --endorser_key_hash or --endorser_keyset_hash must be specified.");
    }

    for endorser_key_hash in endorser_key_hashes {
        list_endorsements(&loader, endorser_key_hash.as_str(), now_utc_millis);
    }
}

fn list_endorser_keys(
    loader: &endorsement_loader::ContentAddressableEndorsementLoader,
    endorser_keyset_hash: &str,
) -> Vec<String> {
    let endorser_keys = loader.list_endorser_keys(endorser_keyset_hash);
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

pub(crate) const MPM_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/31543.md";
const PUBLISHED_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/52637.md";
const RUNNABLE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/68317.md";
const OPEN_SOURCE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/92939.md";

const EXPECTED_CLAIMS: &[&str] =
    &[OPEN_SOURCE_CLAIM_TYPE, RUNNABLE_CLAIM_TYPE, PUBLISHED_CLAIM_TYPE];

fn prettify_claim(claim: &str) -> String {
    match claim {
        MPM_CLAIM_TYPE => format!("{claim} (Distributed as MPM)"),
        OPEN_SOURCE_CLAIM_TYPE => format!("{claim} (Open Source)"),
        RUNNABLE_CLAIM_TYPE => format!("{claim} (Runnable Binary)"),
        PUBLISHED_CLAIM_TYPE => format!("{claim} (Published Binary)"),
        _ => claim.to_string(),
    }
}

fn list_endorsements(
    loader: &endorsement_loader::ContentAddressableEndorsementLoader,
    endorser_key_hash: &str,
    now_utc_millis: i64,
) {
    let endorsement_hashes = loader.list_endorsements(endorser_key_hash);
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

    // The index is append-only so we iterate backwards to show the most recent
    // endorsements first.
    for endorsement_hash in endorsement_hashes.iter().rev() {
        let result = loader
            .load_endorsement(endorsement_hash.as_str())
            .with_context(|| format!("loading endorsement {endorsement_hash}"));

        if result.is_err() {
            println!(
                "❌  Loading endorsement {} failed: {:?}",
                endorsement_hash,
                result.err().unwrap()
            );
        } else {
            let (signed_endorsement, reference_values) = result.unwrap();
            let result = verify_endorsement(now_utc_millis, &signed_endorsement, &reference_values)
                .context("verifying endorsement");
            if result.is_err() {
                println!("    ❌  {endorsement_hash}: {:?}", result.err().unwrap());
            } else {
                println!("    ✅  {endorsement_hash}");
                let details = result.unwrap();
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
                    if !EXPECTED_CLAIMS.contains(&c.as_str()) {
                        println!("        🛄  {}", prettify_claim(&c));
                    }
                }
            }
        }
    }
}

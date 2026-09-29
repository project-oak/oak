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

use std::collections::HashSet;

use anyhow::Context;
use clap::Args;
use endorscope::{
    package::Package,
    storage::{CaStorage, EndorsementLoader},
};
use intoto::statement::Validity;
use oak_digest::{Digest, Sha256};
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
        help = "Specifies that no t-log inclusion (Rekor, C2SP/Sigsum or PES) should be verified."
    )]
    skip_tlog_verification: bool,

    #[arg(
        long,
        help = "Public key to verify Rekor log entries, as PEM. Can be empty. Default is to verify Rekor inclusion, unless overridden by --skip_tlog_verification",
        default_value = get_rekor_v1_public_key_pem(),
    )]
    rekor_public_key: String,

    #[arg(
        long,
        help = "C2SP policy to verify C2SP t-log proofs. Empty by default, so no verification happens.",
        default_value = ""
    )]
    c2sp_policy: String,

    #[arg(
        long,
        help = "Reference value for verifying a PES confirmation. Empty by default, so no verification happens.",
        default_value = ""
    )]
    pes_ref_value: String,

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

/// Represents actual search criteria, all of which are concatenated by a
/// logical AND.
#[derive(Args)]
pub(crate) struct ListMode {
    #[arg(
        long,
        help = "List by typed hash of the endorsed subject.",
        value_parser = parse_typed_hash,
    )]
    subject_hash: Option<String>,

    #[arg(
        long,
        help = "List by typed hash of the verifying key.",
        value_parser = parse_typed_hash,
    )]
    endorser_key_hash: Option<String>,

    #[arg(
        long,
        help = "List by typed hash of the verifying key set.",
        value_parser = parse_typed_hash,
    )]
    endorser_keyset_hash: Option<String>,

    #[arg(long, help = "List by claim.")]
    claim: Vec<String>,
}

/// Parses a typed SHA2-256 hash string into a [`Sha256`] digest.
///
/// Params:
/// - h: The typed hash string (e.g. `sha2-256:<hex>`).
///
/// Returns:
/// - The parsed [`Sha256`] digest.
fn parse_sha256(h: &str) -> Sha256 {
    match Digest::from_typed_hash(h) {
        Ok(Digest::Sha256(d)) => d,
        _ => panic!("invalid sha2-256 hash {h}"),
    }
}

/// Lists endorsements depending on arguments.
///
/// Params:
/// - current_time: The timestamp to use for endorsement verification.
/// - claim_types: Global claim types required to be present on all
///   endorsements.
/// - p: Command-line arguments for the `list` subcommand.
/// - access_token: Optional OAuth access token for storage authentication.
pub(crate) fn list(
    current_time: Instant,
    claim_types: Vec<String>,
    p: ListArgs,
    access_token: Option<String>,
) {
    let storage = CaStorage {
        url_prefix: p.url_prefix,
        fbucket: p.fbucket,
        ibucket: p.ibucket,
        access_token,
    };
    let loader = EndorsementLoader::new(Box::new(storage));

    let mut final_hashes: Option<Vec<String>> = None;
    let mut keyset_keys: Option<Vec<Sha256>> = None;

    let mut intersect = |hashes: Vec<String>| match final_hashes.as_mut() {
        Some(current) => {
            let set: HashSet<String> = hashes.into_iter().collect();
            current.retain(|h| set.contains(h));
        }
        None => {
            final_hashes = Some(hashes);
        }
    };

    if p.mode.subject_hash.is_none()
        && p.mode.endorser_key_hash.is_none()
        && p.mode.endorser_keyset_hash.is_none()
        && p.mode.claim.is_empty()
    {
        panic!("At least one list mode must be specified");
    }

    if let Some(hash) = &p.mode.subject_hash {
        let hashes =
            loader.list_endorsements_by_subject(hash).expect("listing endorsements by subject");
        intersect(hashes);
    }

    if let Some(hash) = &p.mode.endorser_key_hash {
        let hashes = loader.list_endorsements_by_key(hash).expect("listing endorsements by key");
        println!("🧲  Found {} endorsements for endorser key {}", hashes.len(), hash);
        intersect(hashes);
    }

    if let Some(hash) = &p.mode.endorser_keyset_hash {
        let (hashes, keys) = list_endorsements_by_keyset(&loader, hash);
        keyset_keys = Some(keys);
        intersect(hashes);
    }

    for hash in &p.mode.claim {
        let hashes =
            loader.list_endorsements_by_claim(hash).expect("listing endorsements by claim");
        intersect(hashes);
    }

    let (rekor_public_key, c2sp_policy, pes_ref_value) = if p.skip_tlog_verification {
        (None, None, None)
    } else {
        (
            string_to_option_string(p.rekor_public_key),
            string_to_option_string(p.c2sp_policy),
            string_to_option_string(p.pes_ref_value),
        )
    };
    let subject_hash = p.mode.subject_hash.as_deref().map(parse_sha256);
    let endorser_key_hash = p.mode.endorser_key_hash.as_deref().map(parse_sha256);
    list_endorsement_hashes(
        current_time,
        [claim_types, p.mode.claim].concat(),
        subject_hash,
        endorser_key_hash,
        keyset_keys.as_deref(),
        &loader,
        final_hashes.unwrap_or_default(),
        rekor_public_key,
        c2sp_policy,
        pes_ref_value,
        p.limit,
    );
}

/// Lists all endorsement hashes and parsed key digests for an endorser keyset.
///
/// Params:
/// - loader: The endorsement loader to query.
/// - keyset_hash: The typed hash of the endorser keyset.
///
/// Returns:
/// - A tuple of `(endorsement_hashes, keyset_keys)`.
fn list_endorsements_by_keyset(
    loader: &EndorsementLoader,
    keyset_hash: &str,
) -> (Vec<String>, Vec<Sha256>) {
    let keys = list_keys_by_keyset(loader, keyset_hash);
    let mut keyset_hashes = HashSet::new();
    let mut keyset_vec = Vec::new();
    for key_hash in &keys {
        if let Ok(hashes) = loader.list_endorsements_by_key(key_hash) {
            println!("🧲  Found {} endorsements for endorser key {}", hashes.len(), key_hash);
            for h in hashes {
                if keyset_hashes.insert(h.clone()) {
                    keyset_vec.push(h);
                }
            }
        }
    }
    (keyset_vec, keys.iter().map(|k| parse_sha256(k)).collect())
}

/// Loads, verifies, and prints endorsement packages for the given hashes.
///
/// Params:
/// - current_time: The timestamp to use for endorsement verification.
/// - claim_types: Claim types required to be present on all endorsements.
/// - subject_hash: Expected subject digest if filtered by `--subject-hash`.
/// - endorser_key_hash: Expected endorser key digest if filtered by
///   `--endorser-key-hash`.
/// - keyset_keys: Allowed endorser key digests if filtered by
///   `--endorser-keyset-hash`.
/// - loader: The endorsement loader used to fetch each package.
/// - endorsement_hashes: Candidate endorsement hashes to load and verify.
/// - rekor_public_key: Optional Rekor public key PEM for log verification.
/// - c2sp_policy: Optional C2SP policy for t-log proof verification.
/// - pes_ref_value: Optional PES reference value for PES verification.
/// - limit: Maximum number of endorsements to list (unlimited if 0).
#[allow(clippy::too_many_arguments)]
fn list_endorsement_hashes(
    current_time: Instant,
    claim_types: Vec<String>,
    subject_hash: Option<Sha256>,
    endorser_key_hash: Option<Sha256>,
    keyset_keys: Option<&[Sha256]>,
    loader: &EndorsementLoader,
    endorsement_hashes: Vec<String>,
    rekor_public_key: Option<String>,
    c2sp_policy: Option<String>,
    pes_ref_value: Option<String>,
    limit: usize,
) {
    // The index is append-only so we iterate backwards to show the most recent
    // endorsements first.
    for (index, endorsement_hash) in endorsement_hashes.iter().rev().enumerate() {
        let result = loader
            .load(
                endorsement_hash,
                rekor_public_key.clone(),
                c2sp_policy.clone(),
                pes_ref_value.clone(),
            )
            .with_context(|| format!("loading endorsement {endorsement_hash}"));
        match result {
            Ok(package) => verify_print_package(
                current_time,
                claim_types.clone(),
                subject_hash,
                endorser_key_hash,
                keyset_keys,
                &package,
                endorsement_hash,
            ),
            Err(err) => println!("❌  Loading endorsement {} failed: {:?}", endorsement_hash, err),
        }
        if limit > 0 && index >= limit - 1 {
            break;
        }
    }
}

/// Lists and prints all endorser key hashes belonging to an endorser keyset.
///
/// Params:
/// - loader: The endorsement loader to query.
/// - endorser_keyset_hash: The typed hash of the endorser keyset.
///
/// Returns:
/// - The list of typed endorser key hashes in the keyset.
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

/// Verifies an endorsement package and pretty-prints it to stdout.
///
/// Params:
/// - current_time: The timestamp to use for endorsement verification.
/// - claim_types: Claim types required to be present on the endorsement.
/// - subject_hash: Expected subject digest if filtered by `--subject-hash`.
/// - endorser_key_hash: Expected endorser key digest if filtered by
///   `--endorser-key-hash`.
/// - keyset_keys: Allowed endorser key digests if filtered by
///   `--endorser-keyset-hash`.
/// - package: The loaded endorsement package to verify.
/// - endorsement_hash: The typed hash of the endorsement being verified.
fn verify_print_package(
    current_time: Instant,
    claim_types: Vec<String>,
    subject_hash: Option<Sha256>,
    endorser_key_hash: Option<Sha256>,
    keyset_keys: Option<&[Sha256]>,
    package: &Package,
    endorsement_hash: &str,
) {
    let signed_endorsement =
        package.get_signed_endorsement().expect("failed to get signed endorsement");
    let result = verify_endorsement(
        current_time.into_unix_millis(),
        &signed_endorsement,
        &package.get_reference_value(claim_types),
    )
    .context("verifying endorsement")
    .and_then(|res| {
        if let Some(expected) = subject_hash {
            res.0
                .validate_subject_digest(&Digest::from(expected).into())
                .context("validating subject digest")?;
        }
        if let Some(expected) = endorser_key_hash {
            let actual = package.get_endorser_key_hash();
            anyhow::ensure!(
                actual == expected,
                "endorser key hash mismatch: expected {}, got {}",
                expected.to_typed_hash(),
                actual.to_typed_hash()
            );
        }
        if let Some(expected_set) = keyset_keys {
            let actual = package.get_endorser_key_hash();
            anyhow::ensure!(
                expected_set.contains(&actual),
                "endorser key {} not in keyset",
                actual.to_typed_hash()
            );
        }
        Ok(res)
    });
    match result {
        Ok((statement, _tlog_verification)) => {
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
            for c in details.claim_types {
                if c.starts_with(MPM_VERSION_CLAIM_TYPE) {
                    let mpm_version_id =
                        c.strip_prefix(MPM_VERSION_CLAIM_TYPE).unwrap().strip_prefix("?").unwrap();
                    println!("        🛠  {}", mpm_version_id);
                } else {
                    println!("        🛄  {}", prettify_claim(&c));
                }
            }
        }
        Err(err) => println!("    ❌  {endorsement_hash}: {:?}", err),
    }
}

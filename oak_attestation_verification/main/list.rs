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
use oak_attestation_verification::verify_endorsement;

use crate::endorsement_loader;

// Subcommand for listing all endorsements for a given endorser key.
//
// The fbucket_name and ibucket_name are used to determine the storage location
// of the content addressable files and the link index file. The url_prefix can
// be used to override the default storage location (Google Cloud Storage).
//
// Example:
//   list --endorser_key_hash=12345 --fbucket=12345 --ibucket=67890
#[derive(Args)]
pub(crate) struct ListArgs {
    #[arg(long, help = "Content addressable hash of the endorser key used to sign endorsements.")]
    endorser_key_hash: Option<String>,

    #[arg(
        long,
        help = "Content addressable hash of the rotating endorser keyset used to sign endorsements."
    )]
    endorser_keyset_hash: Option<String>,

    #[arg(
        long,
        help = "URL prefix of the content addressable storage.",
        default_value = "https://storage.googleapis.com"
    )]
    url_prefix: String,

    #[arg(long, help = "Bucket name of the content addressable file storage bucket.")]
    fbucket: String,

    #[arg(long, help = "Bucket name of the content addressable index storage bucket.")]
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

    for endorsement_hash in endorsement_hashes {
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
            let (endorsement, reference_values) = result.unwrap();
            let result = verify_endorsement(now_utc_millis, &endorsement, &reference_values)
                .context("verifying endorsement");
            if result.is_err() {
                println!("❌  {endorsement_hash}: {:?}", result.err().unwrap());
            } else {
                println!("✅  {endorsement_hash}");
            }
        }
    }
}

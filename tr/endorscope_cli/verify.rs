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

//! This module implements the `verify` command. It provides subcommands for
//! verifying an endorsement from different sources.
//!
//! The currently supported endorsement sources are:
//! - local: a local file
//! - remote: A remote content addressable storage

use std::{path::PathBuf, sync::Arc};

use anyhow::Context;
use clap::{Args, Subcommand};
use endorscope::{
    ContentAddressableEndorsementLoader, FileEndorsementBuilder, FileEndorsementLoader,
    HTTPContentAddressableStorageBuilder,
};
use oak_proto_rust::oak::attestation::v1::{EndorsementReferenceValue, SignedEndorsement};
use url::Url;
use verify_endorsement::verify_endorsement;

// Subcommands for the verify command.
#[derive(Subcommand)]
pub(crate) enum VerifyCommands {
    #[command(subcommand = "file", about = "Verify an endorsement from a local file.")]
    File(VerifyFileArgs),

    #[command(
        subcommand = "remote",
        about = "Verify an endorsement from a remote content addressable storage."
    )]
    Remote(VerifyRemoteArgs),
}

// Subcommand for verifying an endorsement from a local filesystem.
//
// Example:
//   verify file --endorsement=endorsement.json --signature=endorsement.json.sig
// --endorser_public_key=endorser_public_key.pem
#[derive(Args)]
pub(crate) struct VerifyFileArgs {
    #[arg(long, help = "Path to the endorsement.json to verify.")]
    endorsement: PathBuf,

    #[arg(long, help = "Path to the endorsement.json.sig to verify.")]
    signature: PathBuf,

    #[arg(long, help = "Path to the public key to verify.")]
    endorser_public_key: PathBuf,

    #[arg(long, help = "Path to the subject if needed for the verification.")]
    subject: Option<PathBuf>,

    #[arg(long, help = "Path to the logentry.json to verify, if available.")]
    log_entry: Option<PathBuf>,
}

// Subcommand for verifying an endorsement from a remote content addressable
// storage.
//
// The fbucket_name and ibucket_name are used to determine the storage location
// of the content addressable files and the link index file. The url_prefix can
// be used to override the default storage location (Google Cloud Storage).
//
// Example:
//   verify remote --endorsement_hash=${hash} --fbucket=12345 --ibucket=67890
#[derive(Args)]
pub(crate) struct VerifyRemoteArgs {
    #[arg(
        long,
        help = "Typed hash of the endorsement.",
        value_parser = parse_typed_hash,
    )]
    endorsement_hash: String,

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

// Verifies only the most basic things from
// https://cloud.google.com/storage/docs/buckets#naming
pub(crate) fn parse_bucket_name(arg: &str) -> Result<String, anyhow::Error> {
    if arg.len() < 3 || arg.len() > 222 {
        anyhow::bail!("length of bucket name outside valid range");
    }
    if !arg.chars().all(|c| {
        char::is_ascii_digit(&c) || char::is_ascii_lowercase(&c) || c == '_' || c == '-' || c == '.'
    }) {
        anyhow::bail!("invalid character in bucket name");
    }
    Ok(arg.to_string())
}

// Parses command line arguments that represent URLs.
pub(crate) fn parse_url(arg: &str) -> Result<Url, anyhow::Error> {
    Ok(Url::parse(arg)?)
}

// Rejects anything that does not look like a typed hash, e.g.:
// sha2-256:00bb342c482f7ce24c89a32e0a7c44ae3751e931d7975ac1a27ae630c62cb1e4
pub(crate) fn parse_typed_hash(arg: &str) -> Result<String, anyhow::Error> {
    let mut splitted = arg.split(':');
    if splitted.next() != Some("sha2-256") {
        anyhow::bail!("only SHA2_256 hashes are in use right now");
    }
    let value = splitted.next().ok_or(anyhow::anyhow!("malformed typed hash"))?;
    if value.len() != 2 * 32 {
        anyhow::bail!("bad length of SHA2_256 hash");
    }
    if value.chars().any(|c| !char::is_ascii_hexdigit(&c)) {
        anyhow::bail!("invalid character in hex-encoded hash");
    }
    Ok(arg.to_string())
}

// Verifies an endorsement from a local file.
pub(crate) fn verify_file(p: VerifyFileArgs, now_utc_millis: i64) {
    let loader = FileEndorsementLoader {};

    let params = FileEndorsementBuilder::default()
        .endorsement_path(p.endorsement)
        .signature_path(p.signature)
        .endorser_public_key_path(p.endorser_public_key)
        .log_entry_path(p.log_entry)
        .subject_path(p.subject)
        .build()
        .expect("Failed to build endorsement loader");

    let (endorsement, reference_values) =
        loader.load_endorsement(params).expect("Failed to load endorsement");

    verify(endorsement, reference_values, now_utc_millis);
}

// Verifies an endorsement from a remote content addressable storage.
pub(crate) fn verify_remote(p: VerifyRemoteArgs, now_utc_millis: i64) {
    let storage = HTTPContentAddressableStorageBuilder::default()
        .url_prefix(p.url_prefix)
        .fbucket(p.fbucket)
        .ibucket(p.ibucket)
        .build()
        .expect("Failed to build storage");

    let loader = ContentAddressableEndorsementLoader::new_with_storage(Arc::new(storage));

    let (endorsement, reference_values) =
        loader.load_endorsement(p.endorsement_hash.as_str()).expect("Failed to load endorsement");

    verify(endorsement, reference_values, now_utc_millis);
}

// Verifies an endorsement from a given endorsement loader.
pub(crate) fn verify(
    signed_endorsement: SignedEndorsement,
    ref_values: EndorsementReferenceValue,
    now_utc_millis: i64,
) {
    let result = verify_endorsement(now_utc_millis, &signed_endorsement, &ref_values)
        .context("verifying endorsement");
    if result.is_err() {
        panic!("❌ Verification failed: {:?}", result.err().unwrap());
    }

    println!("✅ OK");
}

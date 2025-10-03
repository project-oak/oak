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

use std::{fs, path::PathBuf};

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use endorscope::{
    package::Package,
    storage::{CaStorage, EndorsementLoader},
};
use oak_time::Instant;
use rekor::get_rekor_v1_public_key_pem;
use url::Url;

/// Subcommands for the verify command.
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

/// Subcommand for verifying an endorsement from a local filesystem.
///
/// Example:
///   verify file --endorsement=endorsement.json
///               --signature=endorsement.json.sig
///               --endorser_public_key=endorser_public_key.pem
#[derive(Args)]
pub(crate) struct VerifyFileArgs {
    #[arg(long, help = "Path to the endorsement.json to verify.")]
    endorsement: PathBuf,

    #[arg(long, help = "Path to the signature file to verify.")]
    signature: PathBuf,

    #[arg(long, help = "Path to the public key to verify.")]
    endorser_public_key: PathBuf,

    #[arg(long, help = "Path to the subject if needed for the verification.")]
    subject: Option<PathBuf>,

    #[arg(
        long,
        help = "Path to the log entry, if the endorsement signature has been committed to a transparency log."
    )]
    log_entry: Option<PathBuf>,
}

// Subcommand for verifying an endorsement from a remote content addressable
// storage.
//
// The `fbucket` and `ibucket` names are used to determine the storage location
// of the content addressable files and the link index file. The `url_prefix`
// can be used to override the default storage location, wich is Google Cloud
// Storage (GCS).
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

impl VerifyFileArgs {
    /// Loads endorsement package from disk into memory.
    pub fn load(&self) -> Result<Package> {
        let endorsement = fs::read(&self.endorsement)
            .with_context(|| format!("reading endorsement from {}", &self.endorsement.display()))?;
        let signature = fs::read(&self.signature)
            .with_context(|| format!("reading signature from {}", &self.signature.display()))?;
        let log_entry = match &self.log_entry {
            None => None,
            Some(path) => Some(
                fs::read(path)
                    .with_context(|| format!("reading log_entry from {}", path.display()))?,
            ),
        };
        let subject = match &self.subject {
            None => None,
            Some(path) => {
                Some(fs::read(path).context(format!("reading subject from {}", path.display()))?)
            }
        };
        let endorser_public_key =
            fs::read_to_string(&self.endorser_public_key).with_context(|| {
                format!("reading endorser public key from {}", self.endorser_public_key.display())
            })?;

        Ok(Package {
            endorsement,
            signature,
            log_entry,
            subject,
            endorser_public_key,
            rekor_public_key: Some(get_rekor_v1_public_key_pem()),
        })
    }
}

/// Verifies an endorsement package from local files.
pub(crate) fn verify_file(current_time: Instant, p: VerifyFileArgs) {
    let package = p.load().expect("Failed to load endorsement");
    display_verify_result(package.verify(current_time.into_unix_millis()));
}

/// Verifies an endorsement package from a remote content addressable storage.
pub(crate) fn verify_remote(current_time: Instant, p: VerifyRemoteArgs) {
    let storage = CaStorage { url_prefix: p.url_prefix, fbucket: p.fbucket, ibucket: p.ibucket };
    let loader = EndorsementLoader::new(Box::new(storage));
    let package = loader.load(p.endorsement_hash.as_str()).expect("Failed to load endorsement");
    display_verify_result(package.verify(current_time.into_unix_millis()));
}

/// Verifies an endorsement from a given endorsement loader.
fn display_verify_result(result: Result<()>) {
    if result.is_err() {
        panic!("❌ Verification failed: {:?}", result.err().unwrap());
    }

    println!("✅ OK");
}

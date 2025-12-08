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

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result};
use clap::Parser;
use digest_util::hex_digest_from_typed_hash;
use intoto::statement::{make_statement, serialize_statement};
use maplit::hashmap;
use oak_proto_rust::oak::HexDigest;
use oak_time::{Duration, Instant};
use oci_spec::image::{Digest, MediaType};

use crate::{
    flags::{self, parse_current_time, parse_duration},
    repository::{prepare_repository, repository_add_file},
};

const TR_TYPE_ANNOTATION: &str = "tr.type";
const TR_SUBJECT_ANNOTATION: &str = "tr.subject";
const TR_ENDORSEMENT_ANNOTATION: &str = "tr.endorsement";

const SUBJECT_TYPE: &str = "subject";
const ENDORSEMENT_TYPE: &str = "endorsement";
const SIGNATURE_TYPE: &str = "signature";

const OCTET_STREAM_MEDIA_TYPE: &str = "application/octet-stream";
const IN_TOTO_MEDIA_TYPE: &str = "application/vnd.in-toto+json";
const SIGSTORE_BUNDLE_MEDIA_TYPE: &str = "application/vnd.dev.sigstore.bundle+json";

// In most cases we don't care about the subject name in the endorsement.
const EMPTY_SUBJECT_NAME: &str = "";

#[derive(Parser, Debug)]
pub struct Endorse {
    #[command(flatten)]
    pub input: Input,

    #[arg(long, help = "Path to the endorsement repository root", required = true)]
    pub repository: PathBuf,

    #[command(flatten)]
    pub claims: flags::Claims,

    #[arg(long, value_parser = parse_duration, help = "A duration string indicating how long the endorsement is valid for, e.g., '30d', '12h', '1w'")]
    pub valid_for: Duration,

    #[arg(
        long,
        help = "A fixed timestamp for issuing the endorsement, in RFC3339 format",
        value_parser = parse_current_time,
        default_value = ""
    )]
    pub issued_on: Instant,
}

#[derive(Parser, Debug)]
#[group(required = true, multiple = false)]
pub struct Input {
    #[arg(long, help = "Path to the file to endorse")]
    pub file: Option<PathBuf>,

    #[arg(long, help = "Digest of the artifact to endorse (e.g., sha256:...)")]
    pub digest: Option<String>,
}

fn oci_digest_to_hex_digest(oci_digest: &Digest) -> Result<HexDigest> {
    hex_digest_from_typed_hash(oci_digest.as_ref())
}

fn store_subject_file(repository_path: &Path, file_path: &Path) -> Result<HexDigest> {
    let file_data = fs::read(file_path).context("Failed to read file")?;
    let desc = repository_add_file(
        repository_path,
        &file_data,
        hashmap! {
            TR_TYPE_ANNOTATION.to_string() => SUBJECT_TYPE.to_string(),
        },
        MediaType::Other(OCTET_STREAM_MEDIA_TYPE.to_string()),
    )?;

    oci_digest_to_hex_digest(desc.digest())
}

impl Endorse {
    pub async fn run(&self) -> Result<()> {
        prepare_repository(&self.repository)?;

        // Obtain the digest of the subject to endorse, either from the input file (in
        // which case stash the file itself in the repo too) or from the user provided
        // digest flag (in which case the repo may not contain the content of the
        // digest).
        let subject_hex_digest = if let Some(path) = &self.input.file {
            store_subject_file(&self.repository, path)?
        } else if let Some(digest_str_ref) = &self.input.digest {
            hex_digest_from_typed_hash(digest_str_ref)?
        } else {
            unreachable!("clap ensures one is present");
        };

        let claims = self
            .claims
            .claims_toml
            .as_ref()
            .map(|c| c.claims.clone())
            .or(self.claims.claims.clone())
            .unwrap();
        if claims.is_empty() {
            anyhow::bail!("at least one claim must be provided");
        }

        let claim_types: Vec<&str> = claims.iter().map(|x| &**x).collect();
        let statement = make_statement(
            EMPTY_SUBJECT_NAME,
            &subject_hex_digest,
            self.issued_on,
            self.issued_on,
            self.issued_on + self.valid_for,
            claim_types,
        );

        let statement_data =
            serialize_statement(&statement).context("Failed to serialize endorsement statement")?;

        let statement_desc = repository_add_file(
            &self.repository,
            &statement_data,
            hashmap! {
                TR_TYPE_ANNOTATION.to_string() => ENDORSEMENT_TYPE.to_string(),
                // This annotation is used to efficiently look up endorsements about a specific digest from a repository index.
                TR_SUBJECT_ANNOTATION.to_string() => format!("sha256:{}", subject_hex_digest.sha2_256),
            },
            MediaType::Other(IN_TOTO_MEDIA_TYPE.to_string()),
        )?;
        let statement_digest_str = statement_desc.digest().digest().to_string();

        // Sign statement (Create Signature Bundle).
        let temp_dir = std::env::temp_dir();

        // The output bundle that cosign will write.
        let temp_bundle_path = temp_dir.join(format!("bundle-{}.json", std::process::id()));

        // The input statement that cosign will read.
        let temp_statement_path = temp_dir.join(format!("statement-{}.json", std::process::id()));
        fs::write(&temp_statement_path, &statement_data)
            .context("Failed to write temp statement")?;

        eprintln!(
                "Calling cosign to create endorsement signature... (please complete OIDC flow if prompted)"
            );
        let mut command = Command::new("cosign");
        command
            .arg("sign-blob")
            .arg(format!("--bundle={}", temp_bundle_path.display()))
            .arg(format!("--oidc-issuer={}", "https://oauth2.sigstore.dev/auth"))
            .arg("--yes")
            .arg(&temp_statement_path);
        eprintln!("Running command: {command:?}");

        let status = command.status().context("Failed to execute cosign")?;

        if !status.success() {
            anyhow::bail!("Cosign failed with status: {status}");
        }

        // Read signature bundle from the temporary file, and add it to the repository.
        let bundle_data = fs::read(&temp_bundle_path).context("Failed to read generated bundle")?;
        repository_add_file(
            &self.repository,
            &bundle_data,
            hashmap! {
                TR_TYPE_ANNOTATION.to_string() => SIGNATURE_TYPE.to_string(),
                TR_ENDORSEMENT_ANNOTATION.to_string() => statement_digest_str,
            },
            MediaType::Other(SIGSTORE_BUNDLE_MEDIA_TYPE.to_string()),
        )?;

        let index_path = self.repository.join("index.json");
        eprintln!("Updated index at {:?}", index_path);

        Ok(())
    }
}

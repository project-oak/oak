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

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Parser;
use intoto::statement::{make_statement, serialize_statement};
use oak_digest::Digest;
use oak_time::{Duration, Instant};
use trex_client::{
    BlobWriter, EndorsementIndexWriter,
    cosign::cosign_sign_blob,
    fs::{FileSystemBlobStore, FileSystemEndorsementIndex},
};

use crate::flags::{self, parse_current_time, parse_duration};

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

async fn store_subject_file(blob_store: &FileSystemBlobStore, file_path: &Path) -> Result<Digest> {
    let file_data = std::fs::read(file_path).context("reading subject file")?;
    blob_store.store_blob(&file_data).await.context("storing subject blob")
}

impl Endorse {
    pub async fn run(&self) -> Result<()> {
        let blob_store = FileSystemBlobStore::new(self.repository.clone());
        blob_store.prepare()?;
        let index = FileSystemEndorsementIndex::new(self.repository.clone());
        index.prepare()?;

        // Obtain the digest of the subject to endorse.
        let subject_digest = if let Some(path) = &self.input.file {
            store_subject_file(&blob_store, path).await?
        } else if let Some(digest_str_ref) = &self.input.digest {
            Digest::from_typed_hash(digest_str_ref)?
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
            &subject_digest.clone().into(),
            self.issued_on,
            self.issued_on,
            self.issued_on + self.valid_for,
            claim_types,
        );

        let statement_data =
            serialize_statement(&statement).context("Failed to serialize endorsement statement")?;

        let statement_hex_digest = blob_store
            .store_blob(&statement_data)
            .await
            .context("storing endorsement statement")?;
        // Update Index: Subject -> Statement
        index
            .add_subject_to_statement(&subject_digest, &statement_hex_digest)
            .await
            .context("updating subject-to-statement index")?;

        // Sign statement (Create Signature Bundle).
        let bundle_data = cosign_sign_blob(&statement_data)?;

        let bundle_hex_digest =
            blob_store.store_blob(&bundle_data).await.context("storing signature bundle")?;

        // Update Index: Statement -> Bundle
        index
            .add_statement_to_bundle(&statement_hex_digest, &bundle_hex_digest)
            .await
            .context("updating statement-to-bundle index")?;

        Ok(())
    }
}

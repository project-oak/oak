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
};

use anyhow::{Context, Result};
use clap::Parser;
use intoto::statement::{make_statement, serialize_statement};
use maplit::hashmap;
use oak_digest::Digest;
use oak_time::{Duration, Instant};
use trex_client::{
    cosign::cosign_sign_blob, OAK_TR_ENDORSEMENT_SUBJECT_DIGEST_ANNOTATION, OAK_TR_TYPE_ANNOTATION,
    OAK_TR_VALUE_ENDORSEMENT, OAK_TR_VALUE_SUBJECT, REKOR_HASHED_REKORD_DATA_HASH_ANNOTATION,
    REKOR_TYPE_HASHED_REKORD,
};

use crate::{
    flags::{self, parse_current_time, parse_duration},
    repository::{prepare_repository, repository_add_file},
};

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

fn store_subject_file(repository_path: &Path, file_path: &Path) -> Result<Digest> {
    let file_data = fs::read(file_path).context("Failed to read file")?;
    let desc = repository_add_file(
        repository_path,
        &file_data,
        hashmap! {
            OAK_TR_TYPE_ANNOTATION.to_string() => vec![OAK_TR_VALUE_SUBJECT.to_string()],
        },
    )?;

    Digest::from_typed_hash(desc.digest.as_ref()).map_err(|e| anyhow::anyhow!(e))
}

impl Endorse {
    pub async fn run(&self) -> Result<()> {
        prepare_repository(&self.repository)?;

        // Obtain the digest of the subject to endorse, either from the input file (in
        // which case stash the file itself in the repo too) or from the user provided
        // digest flag (in which case the repo may not contain the content of the
        // digest).
        let subject_digest = if let Some(path) = &self.input.file {
            store_subject_file(&self.repository, path)?
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

        let statement_desc = repository_add_file(
            &self.repository,
            &statement_data,
            hashmap! {
                OAK_TR_TYPE_ANNOTATION.to_string() => vec![OAK_TR_VALUE_ENDORSEMENT.to_string()],
                // This annotation is used to efficiently look up endorsements about a specific digest from a repository index.
                OAK_TR_ENDORSEMENT_SUBJECT_DIGEST_ANNOTATION.to_string() => vec![subject_digest.to_typed_hash()],
            },
        )?;
        let statement_digest_str = statement_desc.digest.digest().to_string();

        // Sign statement (Create Signature Bundle).
        let bundle_data = cosign_sign_blob(&statement_data)?;

        repository_add_file(
            &self.repository,
            &bundle_data,
            hashmap! {
                OAK_TR_TYPE_ANNOTATION.to_string() => vec![REKOR_TYPE_HASHED_REKORD.to_string()],
                REKOR_HASHED_REKORD_DATA_HASH_ANNOTATION.to_string() => vec![format!("sha256:{}", statement_digest_str)],
            },
        )?;

        let index_path = self.repository.join("index.json");
        eprintln!("Updated index at {:?}", index_path);

        Ok(())
    }
}

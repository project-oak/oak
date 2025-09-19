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

//! Thin wrapper around the `rekor` library. Example invocation on testdata:
//! ```
//! bazel run tr/rekor_cli -- \
//!   --log-entry-path $(pwd)/oak_attestation_verification/testdata/logentry.json \
//!   --artifact-path $(pwd)/oak_attestation_verification/testdata/endorsement.json
//! ```
use std::path::PathBuf;

use anyhow::Context;
use clap::Parser;
use key_util::convert_pem_to_raw;
use rekor::log_entry::verify_rekor_log_entry_ecdsa;

const REKOR_PUBLIC_KEY_PEM: &str =
    include_str!("../../oak_attestation_verification/testdata/rekor_public_key.pem");

#[derive(Parser, Clone)]
#[command(about = "Rekor log entry verification")]
struct Cli {
    #[arg(long, help = "File location of the Rekor log entry.")]
    log_entry_path: PathBuf,

    #[arg(long, help = "File location of the artifact or endorsement.")]
    artifact_path: PathBuf,
}

impl Cli {
    fn log_entry(&self) -> anyhow::Result<Vec<u8>> {
        std::fs::read(self.log_entry_path.clone()).context("reading log entry file")
    }

    fn artifact(&self) -> anyhow::Result<Vec<u8>> {
        std::fs::read(self.artifact_path.clone()).context("reading artifact from file")
    }
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let log_entry = cli.log_entry()?;
    let rekor_public_key = convert_pem_to_raw(REKOR_PUBLIC_KEY_PEM).expect("could not convert key");
    let artifact = cli.artifact()?;

    verify_rekor_log_entry_ecdsa(&log_entry, &rekor_public_key, &artifact)
        .context("verifying log entry")
}

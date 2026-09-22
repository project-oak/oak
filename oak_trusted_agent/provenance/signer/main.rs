//
// Copyright 2026 The Project Oak Authors
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

//! Binds artifacts produced inside Confidential Space to an attestation token.
//!
//! The nonce is the digest of the in-toto Statement, and the token names the
//! image that requested it, so this must run in the same image as the workload
//! that produced the artifacts.

use std::{
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use clap::Parser;
use oak_attestation_gcp::assertions::GcpAssertionGenerator;
use oak_digest::DigestSet;
use oak_trusted_agent_provenance_common::{
    AUDIENCE,
    envelope::Envelope,
    flags,
    statement::{self, Predicate},
};

#[cfg(test)]
mod tests;

#[derive(Parser)]
#[command(about = "Signs an in-toto Statement with a Confidential Space attestation token")]
struct Args {
    /// Artifact to bind, as `name=path` or `path`. Repeatable.
    #[arg(long = "subject", value_parser = flags::parse_named_path)]
    subjects: Vec<(String, PathBuf)>,

    /// Subject that is not a local file, as `name=algorithm:hex`. Repeatable.
    #[arg(long = "subject-digest", value_parser = flags::parse_named_digest)]
    subject_digests: Vec<(String, DigestSet)>,

    /// URI naming the schema of the predicate.
    #[arg(long)]
    predicate_type: String,

    /// JSON object holding the predicate body. Its contents are not
    /// interpreted.
    #[arg(long, value_parser = flags::parse_path)]
    predicate: PathBuf,

    /// Where to write the signed statement.
    #[arg(long, short, value_parser = flags::parse_path)]
    out: PathBuf,

    #[arg(long, default_value = AUDIENCE)]
    audience: String,

    /// Emit an unsigned statement, for testing outside Confidential Space.
    #[arg(long)]
    no_attestation: bool,
}

/// Reads the predicate, which in-toto requires to be a JSON object.
fn read_predicate(path: &Path) -> Result<Predicate> {
    let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_slice(&bytes)
        .context("the predicate must be a JSON object, as in-toto requires")
}

fn main() -> Result<()> {
    let args = Args::parse();

    let subjects = statement::subjects_from_paths(&args.subjects, args.subject_digests)?;
    let statement =
        statement::new(subjects, args.predicate_type, read_predicate(&args.predicate)?)?;

    let generator = (!args.no_attestation)
        .then(|| GcpAssertionGenerator::new(args.audience, /* endorsement= */ None));
    if generator.is_none() {
        eprintln!("--no-attestation: this statement carries no proof and no verifier accepts it");
    }
    let envelope = Envelope::new(&statement, generator.as_ref().map(|g| g as _)).context(
        "could not obtain an attestation token; this binary must run inside Confidential Space, \
         or be given --no-attestation",
    )?;

    envelope.write(&args.out)?;
    eprintln!("wrote {} binding {} subject(s)", args.out.display(), statement.subject.len());
    Ok(())
}

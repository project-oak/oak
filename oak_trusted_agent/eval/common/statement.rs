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

//! Building in-toto Statements, and checking the artifacts they name.
//!
//! Both sides are here so the signer and the verifier cannot drift on the
//! digest algorithm or its spelling.
//!
//! See <https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md>.

use std::{fs, path::PathBuf};

use anyhow::{Context, Result, anyhow};
use intoto::statement::{Statement, Subject};
use oak_digest::{
    DigestSet, MatchResult, Sha256, get_hex_digest_match, hex_to_set_digest, set_to_hex_digest,
};
use oak_proto_rust::oak::HexDigest;

pub const IN_TOTO_TYPE: &str = "https://in-toto.io/Statement/v1";

/// Never interpreted here, so adding a benchmark is a script that emits JSON
/// rather than a change to this crate.
pub type Predicate = serde_json::Map<String, serde_json::Value>;

/// An in-toto Statement carrying an uninterpreted predicate.
///
/// A type alias rather than a struct, so the functions below are free rather
/// than methods: `Statement` belongs to `//tr/intoto` and Rust forbids an
/// inherent impl on a foreign type (E0116).
pub type InTotoStatement = Statement<Predicate>;

/// Builds a statement, rejecting what in-toto forbids so a malformed one is
/// never signed.
pub fn new(
    subject: Vec<Subject>,
    predicate_type: String,
    predicate: Predicate,
) -> Result<InTotoStatement> {
    if subject.is_empty() {
        return Err(anyhow!("a statement needs at least one subject"));
    }
    if predicate_type.is_empty() {
        return Err(anyhow!("predicateType is required and must be a URI"));
    }
    let mut names: Vec<&str> = subject.iter().map(|s| s.name.as_str()).collect();
    names.sort_unstable();
    if names.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(anyhow!("subject names must be unique"));
    }
    Ok(Statement { _type: IN_TOTO_TYPE.to_string(), predicate_type, subject, predicate })
}

/// Hashes `contents` under the one algorithm this tooling records. Not
/// `oak_digest::hex_digest_from_contents`, which also computes SHA-384 and
/// SHA-512 that nothing compares.
fn digest_of(contents: &[u8]) -> HexDigest {
    HexDigest { sha2_256: Sha256::from_contents(contents).to_hex(), ..Default::default() }
}

/// Hashes `contents` into a subject, with the algorithm spelled the way
/// in-toto does rather than the way the Oak protos do.
pub fn subject(name: &str, contents: &[u8]) -> Subject {
    Subject { name: name.to_string(), digest: hex_to_set_digest(&digest_of(contents)) }
}

/// Reads and hashes each path, then appends subjects known only by digest,
/// such as a model too large to hash here.
pub fn subjects_from_paths(
    paths: &[(String, PathBuf)],
    digests: impl IntoIterator<Item = (String, DigestSet)>,
) -> Result<Vec<Subject>> {
    let mut subjects = Vec::with_capacity(paths.len());
    for (name, path) in paths {
        let contents = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        subjects.push(subject(name, &contents));
    }
    subjects.extend(digests.into_iter().map(|(name, digest)| Subject { name, digest }));
    Ok(subjects)
}

/// Compares an artifact against what the statement records for it. Proves only
/// that the bytes on disk are the bytes that were hashed; whether anything
/// vouches for the statement is the workload check's question.
///
/// A statement recording nothing this tool can compute is rejected rather than
/// quietly accepted. This is `oak_digest::is_hex_digest_match` with messages an
/// operator can act on.
pub fn check_digest(statement: &InTotoStatement, name: &str, contents: &[u8]) -> Result<()> {
    let found = statement
        .subject
        .iter()
        .find(|subject| subject.name == name)
        .with_context(|| format!("the statement has no subject named {name}"))?;
    let claimed = set_to_hex_digest(&found.digest).context("reading the recorded digest")?;
    match get_hex_digest_match(&digest_of(contents), &claimed) {
        MatchResult::Same => Ok(()),
        MatchResult::Different => Err(anyhow!("the file does not match its digest")),
        MatchResult::Undecidable => {
            Err(anyhow!("the statement records no digest this verifier can check"))
        }
        MatchResult::Contradictory => Err(anyhow!("the recorded digests disagree with each other")),
    }
}

/// Names every subject the caller neither re-hashed nor waived.
pub fn unaccounted<'a>(
    statement: &'a InTotoStatement,
    accounted: impl IntoIterator<Item = &'a str>,
) -> Vec<&'a str> {
    let accounted: std::collections::BTreeSet<&str> = accounted.into_iter().collect();
    statement
        .subject
        .iter()
        .map(|subject| subject.name.as_str())
        .filter(|name| !accounted.contains(name))
        .collect()
}

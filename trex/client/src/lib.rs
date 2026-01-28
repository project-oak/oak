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

//! Client library for Oak Transparent Release (TR) endorsement verification.
//!
//! This crate provides the core abstractions and implementations for looking up
//! and verifying [Transparent Release][tr] endorsements for software artifacts.
//!
//! # Architecture
//!
//! The crate is built around a small set of traits that separate index lookups
//! from blob storage, allowing different backends:
//!
//! - **[`EndorsementIndex`]** / **[`BlobFetcher`]** – read-only traits for
//!   looking up endorsement digests and fetching blob content.
//! - **[`EndorsementIndexWriter`]** / **[`BlobWriter`]** – extension traits for
//!   backends that also support writes (e.g. the filesystem backend).
//!
//! Two concrete backend implementations are provided:
//!
//! | Backend | Module | Use case |
//! |---------|--------|----------|
//! | HTTP    | [`http`] | Remote verification against an OCI-like repository served over HTTP |
//! | Filesystem | [`fs`] | Local endorsement creation and offline verification |
//!
//! # Verification workflow
//!
//! The main entry point for verification is [`EndorsementVerifier::verify`],
//! which implements the following steps:
//!
//! 1. Look up candidate endorsement statements for the subject digest.
//! 2. For each candidate, fetch the endorsement blob and its Rekor signature
//!    bundles from the index.
//! 3. Verify the Cosign signature (via the [`cosign`] module) against the
//!    signer's OIDC identity.
//! 4. Validate the in-toto statement: check the subject digest, validity
//!    period, and required claims.
//!
//! [tr]: https://project-oak.github.io/oak/tr/endorsement/v1

#![feature(exit_status_error)]

use anyhow::{Context, Result, anyhow};
use async_trait::async_trait;
use intoto::statement::DefaultStatement;
use oak_digest::Digest;
use oak_time::Instant;

pub mod cosign;
pub mod fs;
pub mod http;

/// Index name for the subject → endorsement-statement mapping.
pub const SUBJECT_TO_STATEMENT_INDEX: &str = "z02559989796713244320";

/// Index name for the endorsement-statement → signature-bundle mapping.
pub const STATEMENT_TO_BUNDLE_INDEX: &str = "z05735596614295417312";

/// Parses a newline-separated index body into a list of [`Digest`] values.
///
/// Each non-empty line is expected to be a typed hash (e.g. `sha256:abcdef…`).
/// Empty and whitespace-only lines are silently skipped.
pub fn parse_index(body: &str) -> Result<Vec<Digest>> {
    body.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| Digest::from_typed_hash(line.trim()).context("parsing index entry"))
        .collect()
}

/// Trait for looking up endorsements and signatures from an index.
#[async_trait]
pub trait EndorsementIndex {
    /// Looks up endorsements for the given subject digest.
    async fn lookup_endorsements(&self, subject_digest: &Digest) -> Result<Vec<Digest>>;
    /// Looks up signatures (hashed Rekor entries) for the given endorsement
    /// digest.
    async fn lookup_rekor_signatures(&self, endorsement_digest: &Digest) -> Result<Vec<Digest>>;
}

/// Trait for fetching blob content.
#[async_trait]
pub trait BlobFetcher {
    /// Fetches the blob content for the given digest.
    ///
    /// All implementations must confirm that the returned data matches the
    /// input digest.
    async fn fetch_blob(&self, digest: &Digest) -> Result<Vec<u8>>;
}

/// Extension trait for indices that support write operations.
#[async_trait]
pub trait EndorsementIndexWriter: EndorsementIndex {
    /// Adds a mapping from subject → endorsement statement.
    async fn add_subject_to_statement(&self, subject: &Digest, statement: &Digest) -> Result<()>;

    /// Adds a mapping from statement → signature bundle.
    async fn add_statement_to_bundle(&self, statement: &Digest, bundle: &Digest) -> Result<()>;
}

/// Extension trait for blob stores that support write operations.
#[async_trait]
pub trait BlobWriter: BlobFetcher {
    /// Stores a blob and returns its digest.
    async fn store_blob(&self, content: &[u8]) -> Result<Digest>;
}

/// Verifier for Oak endorsements.
pub struct EndorsementVerifier {
    index: Box<dyn EndorsementIndex + Send + Sync>,
    fetcher: Box<dyn BlobFetcher + Send + Sync>,
}

impl EndorsementVerifier {
    /// Creates a new `EndorsementVerifier`.
    pub fn new(
        index: Box<dyn EndorsementIndex + Send + Sync>,
        fetcher: Box<dyn BlobFetcher + Send + Sync>,
    ) -> Self {
        Self { index, fetcher }
    }

    /// Verifies an endorsement for the given subject.
    ///
    /// For `cert_oidc_issuer`, the following values are the most common ones:
    /// - Google -> `https://accounts.google.com`
    /// - Microsoft -> `https://login.microsoftonline.com`
    /// - GitHub -> `https://github.com/login/oauth`
    /// - GitLab -> `https://gitlab.com.`
    ///
    /// For `cert_identity`, the value is usually an email address or username
    /// from the OIDC issuer.
    ///
    /// See https://docs.sigstore.dev/cosign/verifying/verify/#keyless-verification-using-openid-connect for more details about the `cert_identity` and `cert_oidc_issuer` parameters.
    pub async fn verify(
        &self,
        subject_digest: &Digest,
        valid_at: Instant,
        required_claims: &[String],
        cert_identity: &str,
        cert_oidc_issuer: &str,
    ) -> Result<DefaultStatement> {
        let subject_digest_str = subject_digest.to_typed_hash();
        log::info!("Starting verification for subject: {}", subject_digest_str);

        let endorsement_digests = self
            .index
            .lookup_endorsements(subject_digest)
            .await
            .context("looking up endorsements")?;

        if endorsement_digests.is_empty() {
            log::warn!("No endorsements found for subject {:?}", subject_digest);
            anyhow::bail!("no endorsements found for subject {:?}", subject_digest);
        }

        log::info!("Found {} potential matching endorsement statements", endorsement_digests.len());

        for endorsement_digest in endorsement_digests {
            let endorsement_digest_str = endorsement_digest.to_typed_hash();
            log::debug!("Verifying endorsement candidate: {}", endorsement_digest_str);

            // Attempt to verify this endorsement candidate.
            match self
                .verify_candidate(
                    subject_digest,
                    &endorsement_digest,
                    valid_at,
                    required_claims,
                    cert_identity,
                    cert_oidc_issuer,
                )
                .await
            {
                Ok(statement) => {
                    log::info!("Successfully verified endorsement: {}", endorsement_digest_str);
                    return Ok(statement);
                }
                Err(e) => {
                    log::warn!(
                        "Failed to verify endorsement candidate {:?}: {:?}",
                        endorsement_digest,
                        e
                    );
                    continue;
                }
            }
        }

        log::error!("All matching endorsements failed verification");
        anyhow::bail!("no valid endorsement found")
    }

    /// Attempts to verify a single endorsement candidate.
    ///
    /// Fetches the endorsement blob and its associated Rekor signature bundles,
    /// then tries each signature until one passes `cosign verify-blob`. On
    /// success, validates the in-toto statement contents.
    async fn verify_candidate(
        &self,
        subject_digest: &Digest,
        endorsement_digest: &Digest,
        valid_at: Instant,
        required_claims: &[String],
        cert_identity: &str,
        cert_oidc_issuer: &str,
    ) -> Result<DefaultStatement> {
        let endorsement_bytes = self
            .fetcher
            .fetch_blob(endorsement_digest)
            .await
            .context("fetching endorsement blob")?;

        let signature_digests = self
            .index
            .lookup_rekor_signatures(endorsement_digest)
            .await
            .context("looking up signatures")?;

        if signature_digests.is_empty() {
            log::warn!("No signatures found for endorsement");
            anyhow::bail!("no signatures found for endorsement");
        }

        log::debug!("Found {} signatures for endorsement", signature_digests.len());

        let mut last_error = anyhow!("no signatures");

        for signature_digest in signature_digests {
            let signature_digest_str = signature_digest.to_typed_hash();
            log::debug!("Verifying signature: {}", signature_digest_str);
            let bundle_bytes = self
                .fetcher
                .fetch_blob(&signature_digest)
                .await
                .context("fetching signature bundle")?;

            match cosign::cosign_verify_blob(
                cert_identity,
                cert_oidc_issuer,
                &bundle_bytes,
                &endorsement_bytes,
            ) {
                Ok(()) => {
                    log::info!("Signature verified: {}", signature_digest_str);
                    // Signature verified, now check the endorsement content.
                    return self.validate_statement(
                        &endorsement_bytes,
                        subject_digest,
                        valid_at,
                        required_claims,
                    );
                }
                Err(e) => {
                    log::warn!("Failed to verify signature {}: {}", signature_digest_str, e);
                    last_error = e;
                    continue;
                }
            }
        }

        Err(last_error.context("verifying signatures"))
    }

    /// Parses and validates an in-toto endorsement statement.
    ///
    /// Checks that the statement's subject matches `subject_digest`, the
    /// current time falls within the validity window, and all
    /// `required_claims` are present.
    fn validate_statement(
        &self,
        endorsement_bytes: &[u8],
        subject_digest: &Digest,
        valid_at: Instant,
        required_claims: &[String],
    ) -> Result<DefaultStatement> {
        let statement: DefaultStatement = intoto::statement::parse_statement(endorsement_bytes)
            .context("parsing endorsement statement")?;

        let claim_refs: Vec<&str> = required_claims.iter().map(|s| s.as_str()).collect();

        // Validate the statement (subject match, validity period, claims).
        // Statement::validate expects `digest: Option<HexDigest>`, so we
        // convert via the From<Digest> for HexDigest impl.
        statement
            .validate(Some(subject_digest.clone().into()), valid_at, &claim_refs)
            .context("validating endorsement statement")?;

        Ok(statement)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Case {
        name: &'static str,
        input: String,
        expected: Result<Vec<String>, ()>,
    }

    #[test]
    fn test_parse_index() {
        let hash_a = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
        let hash_b = "1111111111111111111111111111111111111111111111111111111111111111";

        let cases: Vec<Case> = vec![
            Case { name: "empty input", input: String::new(), expected: Ok(vec![]) },
            Case { name: "only empty lines", input: "\n\n\n".into(), expected: Ok(vec![]) },
            Case {
                name: "only whitespace lines",
                input: "  \n  \n\t\n".into(),
                expected: Ok(vec![]),
            },
            Case {
                name: "single sha256 entry",
                input: format!("sha256:{hash_a}\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}")]),
            },
            Case {
                name: "single sha2-256 entry",
                input: format!("sha2-256:{hash_a}\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}")]),
            },
            Case {
                name: "multiple sha256 entries",
                input: format!("sha256:{hash_a}\nsha256:{hash_b}\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}"), format!("sha2-256:{hash_b}")]),
            },
            Case {
                name: "multiple sha2-256 entries",
                input: format!("sha2-256:{hash_a}\nsha2-256:{hash_b}\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}"), format!("sha2-256:{hash_b}")]),
            },
            Case {
                name: "mixed sha256 and sha2-256",
                input: format!("sha256:{hash_a}\nsha2-256:{hash_b}\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}"), format!("sha2-256:{hash_b}")]),
            },
            Case {
                name: "valid and empty lines interleaved",
                input: format!("\nsha256:{hash_a}\n\nsha2-256:{hash_b}\n\n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}"), format!("sha2-256:{hash_b}")]),
            },
            Case {
                name: "trims whitespace",
                input: format!("  sha2-256:{hash_a}  \n"),
                expected: Ok(vec![format!("sha2-256:{hash_a}")]),
            },
            Case {
                name: "no trailing newline",
                input: format!("sha2-256:{hash_a}"),
                expected: Ok(vec![format!("sha2-256:{hash_a}")]),
            },
            Case { name: "invalid entry", input: "not_a_valid_digest\n".into(), expected: Err(()) },
            Case {
                name: "valid then invalid",
                input: format!("sha2-256:{hash_a}\ngarbage\n"),
                expected: Err(()),
            },
        ];

        for case in &cases {
            let result = parse_index(&case.input);
            match &case.expected {
                Ok(expected_hashes) => {
                    let digests = result
                        .unwrap_or_else(|e| panic!("{}: expected Ok, got Err: {e}", case.name));
                    let actual: Vec<String> = digests.iter().map(|d| d.to_typed_hash()).collect();
                    assert_eq!(&actual, expected_hashes, "{}", case.name);
                }
                Err(()) => {
                    assert!(result.is_err(), "{}: expected Err, got Ok", case.name);
                }
            }
        }
    }
}

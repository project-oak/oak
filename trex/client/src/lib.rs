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

#![feature(exit_status_error)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use intoto::statement::DefaultStatement;
use oak_proto_rust::oak::HexDigest;
use oak_time::Instant;
use oci_spec::image::Descriptor;

pub mod cosign;
pub mod http;

pub const OAK_TR_ENDORSEMENT_SUBJECT_DIGEST_ANNOTATION: &str = "oak.tr.endorsement.subject_digest";
pub const OAK_TR_TYPE_ANNOTATION: &str = "oak.tr.type";
pub const OAK_TR_ENDORSEMENT_ANNOTATION: &str = "oak.tr.endorsement";

pub const REKOR_HASHED_REKORD_DATA_HASH_ANNOTATION: &str = "rekor.hashedrekord.data_hash";

pub const OAK_TR_VALUE_SUBJECT: &str = "oak.tr.subject";
pub const OAK_TR_VALUE_ENDORSEMENT: &str = "oak.tr.endorsement";
pub const REKOR_TYPE_HASHED_REKORD: &str = "rekor.hashedrekord";

/// Returns true if the descriptor is an Oak endorsement for the given subject
/// digest.
///
/// An Oak endorsement is identified by:
/// 1. `oak.tr.type` annotation set to `oak.tr.endorsement`.
/// 2. `oak.tr.endorsement.subject_digest` annotation matching the given subject
///    digest.
pub fn is_oak_endorsement(entry: &Descriptor, subject_digest: &str) -> bool {
    let annotations = entry.annotations().clone().unwrap_or_default();
    annotations.get(OAK_TR_TYPE_ANNOTATION) == Some(&OAK_TR_VALUE_ENDORSEMENT.to_string())
        && annotations.get(OAK_TR_ENDORSEMENT_SUBJECT_DIGEST_ANNOTATION)
            == Some(&subject_digest.to_string())
}

/// Returns true if the descriptor is a hashed Rekor entry (signature) for the
/// given endorsement digest.
///
/// A hashed Rekor entry is identified by:
/// 1. `oak.tr.type` annotation set to `rekor.hashedrekord`.
/// 2. `rekor.hashedrekord.data_hash` annotation matching the given endorsement
///    digest.
pub fn is_hashed_rekord(entry: &Descriptor, endorsement_digest: &str) -> bool {
    let annotations = entry.annotations().clone().unwrap_or_default();
    annotations.get(OAK_TR_TYPE_ANNOTATION) == Some(&REKOR_TYPE_HASHED_REKORD.to_string())
        && annotations.get(REKOR_HASHED_REKORD_DATA_HASH_ANNOTATION)
            == Some(&endorsement_digest.to_string())
}

/// Trait for looking up endorsements and signatures from an index.
#[async_trait]
pub trait EndorsementIndex {
    /// Looks up endorsements for the given subject digest.
    async fn lookup_oak_tr_endorsements(
        &self,
        subject_digest: &HexDigest,
    ) -> Result<Vec<HexDigest>>;
    /// Looks up signatures (hashed Rekor entries) for the given endorsement
    /// digest.
    async fn lookup_rekor_signatures(
        &self,
        endorsement_digest: &HexDigest,
    ) -> Result<Vec<HexDigest>>;
}

/// Trait for fetching blob content.
#[async_trait]
pub trait BlobFetcher {
    /// Fetches the blob content for the given digest.
    ///
    /// All implementations must confirm that the returned data matches the
    /// input digest.
    async fn fetch_blob(&self, digest: &HexDigest) -> Result<Vec<u8>>;
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
        subject_digest: &HexDigest,
        valid_at: Instant,
        required_claims: &[String],
        cert_identity: &str,
        cert_oidc_issuer: &str,
    ) -> Result<DefaultStatement> {
        let subject_digest_str = format!("sha256:{}", subject_digest.sha2_256);
        log::info!("Starting verification for subject: {}", subject_digest_str);

        let endorsement_digests = self
            .index
            .lookup_oak_tr_endorsements(subject_digest)
            .await
            .context("looking up endorsements")?;

        if endorsement_digests.is_empty() {
            log::warn!("No endorsements found for subject {:?}", subject_digest);
            anyhow::bail!("no endorsements found for subject {:?}", subject_digest);
        }

        log::info!("Found {} potential matching endorsement statements", endorsement_digests.len());

        for endorsement_digest in endorsement_digests {
            let endorsement_digest_str = format!("sha256:{}", endorsement_digest.sha2_256);
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

    async fn verify_candidate(
        &self,
        subject_digest: &HexDigest,
        endorsement_digest: &HexDigest,
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
            let signature_digest_str = format!("sha256:{}", signature_digest.sha2_256);
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

    fn validate_statement(
        &self,
        endorsement_bytes: &[u8],
        subject_digest: &HexDigest,
        valid_at: Instant,
        required_claims: &[String],
    ) -> Result<DefaultStatement> {
        let statement: DefaultStatement = intoto::statement::parse_statement(endorsement_bytes)
            .context("parsing endorsement statement")?;

        let claim_refs: Vec<&str> = required_claims.iter().map(|s| s.as_str()).collect();

        // Validate the statement (subject match, validity period, claims).
        // Note: Statement::validate expects `digest: Option<HexDigest>`.
        // We need to pass the subject digest we are looking for.
        statement
            .validate(Some(subject_digest.clone()), valid_at, &claim_refs)
            .context("validating endorsement statement")?;

        Ok(statement)
    }
}

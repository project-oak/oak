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

//! Who produced the artifacts, according to Confidential Space.

use anyhow::{Context, Result, anyhow};
use jwt::Token;
use oak_attestation_gcp::{
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
    assertions::GcpAssertionVerifier,
    jwt::{Claims, Header},
};
use oak_attestation_verification_types::assertion_verifier::AssertionVerifier;
use oak_proto_rust::oak::attestation::v1::{
    Assertion, ConfidentialSpaceAssertion, ConfidentialSpaceReferenceValues,
    confidential_space_reference_values::ContainerImage,
};
use oak_time::Instant;
use oak_trusted_agent_eval_common::envelope::Envelope;
use oci_spec::distribution::Reference as OciReference;
use prost::Message;

/// Accepts any workload image published under `prefix`, and nothing else.
fn confidential_space_reference_values(prefix: String) -> ConfidentialSpaceReferenceValues {
    ConfidentialSpaceReferenceValues {
        root_certificate_pem: CONFIDENTIAL_SPACE_ROOT_CERT_PEM.to_string(),
        container_image: Some(ContainerImage::ContainerImageReferencePrefix(prefix)),
    }
}

/// The container the Confidential Space token was issued to.
pub struct Workload {
    pub issued_at: Instant,
    /// Digest appended, which is what [`GcpAssertionVerifier`] prefix-matches,
    /// so what is printed is what was checked.
    pub image_reference: OciReference,
    pub image_digest: String,
}

impl Workload {
    /// Verifies that a Confidential Space token binds exactly `payload`, and
    /// was issued to an image published under `image_prefix` and nothing else.
    pub fn from_verified_token(
        envelope: &Envelope,
        payload: &[u8],
        audience: String,
        image_prefix: String,
    ) -> Result<Self> {
        let assertion = envelope.decode_assertion()?;
        let workload = Self::parse_unverified(&assertion)?;
        GcpAssertionVerifier {
            audience,
            reference_values: confidential_space_reference_values(image_prefix),
        }
        .verify(&assertion, payload, workload.issued_at)
        .map_err(|e| anyhow!("{e:?}"))?;
        Ok(workload)
    }

    /// Reads the claims without verifying the token.
    ///
    /// Tokens expire after about an hour, so `issued_at` is what a stored
    /// statement must be verified at, and we need it before we can verify.
    /// Never reuse this for a live session, where the current time is the only
    /// safe choice.
    fn parse_unverified(assertion: &Assertion) -> Result<Self> {
        let cs_assertion = ConfidentialSpaceAssertion::decode(assertion.content.as_slice())
            .context("parsing the Confidential Space assertion")?;
        let jwt = String::from_utf8(cs_assertion.jwt_token).context("the JWT is not UTF-8")?;
        let token: Token<Header, Claims, _> =
            Token::parse_unverified(&jwt).context("parsing the JWT")?;
        let claims = token.claims();
        Ok(Self {
            issued_at: claims.issued_at,
            image_reference: claims
                .effective_reference()
                .context("parsing the OCI container reference")?,
            image_digest: claims.submods.container.image_digest.clone(),
        })
    }
}

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

use endorsement::intoto::EndorsementStatement;
use oak_proto_rust::oak::attestation::v1::{EndorsementReferenceValue, SignedEndorsement};
use oak_time::Instant;
use oci_spec::distribution::Reference;
use p256::ecdsa::VerifyingKey;
use sigstore::{
    message::{SignedMessage, Unverified},
    rekor::{
        hashedrekord::{self, HashedRekord},
        RekorPayload,
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CosignVerificationError {
    #[error("missing workload endorsement data")]
    MissingEndorsement,
    #[error("missing workload endorsement signature")]
    MissingSignature,
    #[error("statement verification error: {0}")]
    StatementVerificationError(sigstore::error::Error),
    #[error("endorsement validation error: {0}")]
    StatementValidationError(String),
    #[error("Endorsement deserialization error: {0}")]
    StatementParseError(serde_json::Error),
    #[error("invalid image reference: {0}")]
    ImageReferenceError(String),
    #[error("rekor error {0}: {1}")]
    RekorError(&'static str, sigstore::error::Error),
    #[error("rekor payload deserialization error: {0}")]
    RekorPayloadParseError(serde_json::Error),
}

pub struct CosignEndorsement {
    statement: SignedMessage<Unverified>,
    rekor: Option<SignedMessage<Unverified>>,
}

impl CosignEndorsement {
    pub fn partial(statement: SignedMessage<Unverified>) -> Self {
        Self { statement, rekor: None }
    }

    pub fn full(statement: SignedMessage<Unverified>, rekor: SignedMessage<Unverified>) -> Self {
        Self { statement, rekor: Some(rekor) }
    }

    pub fn from_bytes_partial(statement: Vec<u8>, signature: Vec<u8>) -> Self {
        let statement = SignedMessage::unverified(statement, signature);
        Self { statement, rekor: None }
    }

    pub fn from_bytes_full(
        statement: Vec<u8>,
        signature: Vec<u8>,
        rekor: Vec<u8>,
    ) -> Result<Self, CosignVerificationError> {
        let statement = SignedMessage::unverified(statement, signature);
        let rekor = sigstore::rekor::from_cosign_bundle(rekor)
            .map_err(|err| CosignVerificationError::RekorError("parsing cosign bundle", err))?;
        Ok(Self { statement, rekor: Some(rekor) })
    }

    pub fn from_proto(proto: &SignedEndorsement) -> Result<Self, CosignVerificationError> {
        let statement: Vec<u8> = match &proto.endorsement {
            Some(data) => data.serialized.clone(),
            None => return Err(CosignVerificationError::MissingEndorsement),
        };
        let signature: Vec<u8> = match &proto.signature {
            Some(data) => data.raw.clone(),
            None => return Err(CosignVerificationError::MissingSignature),
        };

        match proto.rekor_log_entry.len() {
            0 => Ok(Self::from_bytes_partial(statement, signature)),
            _ => Self::from_bytes_full(statement, signature, proto.rekor_log_entry.clone()),
        }
    }
}

pub struct CosignReferenceValues {
    developer_public_key: VerifyingKey,
    rekor_public_key: Option<VerifyingKey>,
}

impl CosignReferenceValues {
    pub fn partial(developer_public_key: VerifyingKey) -> Self {
        Self { developer_public_key, rekor_public_key: None }
    }

    pub fn full(developer_public_key: VerifyingKey, rekor_public_key: VerifyingKey) -> Self {
        Self { developer_public_key, rekor_public_key: Some(rekor_public_key) }
    }

    pub fn from_proto(_proto: &EndorsementReferenceValue) -> Result<Self, CosignVerificationError> {
        Err(CosignVerificationError::MissingEndorsement)
    }
}

pub fn report_endorsement(
    endorsement: CosignEndorsement,
    image_reference: &Reference,
    ref_values: &CosignReferenceValues,
    verification_time: Instant,
) -> Result<(), CosignVerificationError> {
    let statement = (endorsement.statement)
        .verify(&ref_values.developer_public_key)
        .map_err(CosignVerificationError::StatementVerificationError)?;
    let parsed_statement: EndorsementStatement = serde_json::from_slice(statement.message())
        .map_err(CosignVerificationError::StatementParseError)?;

    let subject = image_reference.try_into().map_err(|err: anyhow::Error| {
        CosignVerificationError::ImageReferenceError(err.to_string())
    })?;
    parsed_statement
        .validate(verification_time, &subject, &[])
        .map_err(|err| CosignVerificationError::StatementValidationError(err.to_string()))?;

    if let Some(rekor_public_key) = &ref_values.rekor_public_key {
        if let Some(rekor) = endorsement.rekor {
            let rekor = rekor.verify(rekor_public_key).map_err(|err| {
                CosignVerificationError::RekorError("verifying rekor bundle", err)
            })?;
            let rekor: RekorPayload = serde_json::from_slice(rekor.message())
                .map_err(CosignVerificationError::RekorPayloadParseError)?;
            let hashed_rekord: HashedRekord<hashedrekord::Unverified> =
                rekor.payload_body().map_err(|err| {
                    CosignVerificationError::RekorError("parsing hashedrekord payload", err)
                })?;
            hashed_rekord.verify(&ref_values.developer_public_key, statement.message()).map_err(
                |err| CosignVerificationError::RekorError("verifying rekor payload", err),
            )?;
        } else {
            return Err(CosignVerificationError::MissingEndorsement);
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use oak_file_utils::{read_testdata, read_testdata_string};
    use oak_time::Instant;
    use p256::pkcs8::DecodePublicKey;

    use super::*;

    #[test]
    fn report_endorsement_ok() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: Reference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let endorsement = CosignEndorsement::from_bytes_partial(
            read_testdata!("endorsement.json"),
            read_testdata!("endorsement_signature.sig"),
        );
        let developer_public_key =
            VerifyingKey::from_public_key_pem(&read_testdata_string!("developer_key.pub.pem"))
                .unwrap();

        let result = report_endorsement(
            endorsement,
            &image_reference,
            &CosignReferenceValues::partial(developer_public_key),
            verification_time,
        );
        assert_that!(result, ok(()));
    }

    #[test]
    fn report_endorsement_invalid_signature() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: Reference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let endorsement = CosignEndorsement::from_bytes_partial(
            read_testdata!("endorsement.json"),
            read_testdata!("other_endorsement_signature.sig"),
        );
        let developer_public_key =
            VerifyingKey::from_public_key_pem(&read_testdata_string!("developer_key.pub.pem"))
                .unwrap();

        let result = report_endorsement(
            endorsement,
            &image_reference,
            &CosignReferenceValues::partial(developer_public_key),
            verification_time,
        );
        assert_that!(result, err(anything()));
    }

    #[test]
    fn report_endorsement_with_valid_policy() {
        let verification_time = Instant::from_unix_seconds(1740000000);
        let image_reference: Reference =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app@sha256:313b8a83d3c8bfc9abcffee4f538424473e2705383a7e46f16d159faf0e5ef34"
                .try_into()
                .unwrap();
        let endorsement = CosignEndorsement::from_bytes_partial(
            read_testdata!("endorsement.json"),
            read_testdata!("endorsement_signature.sig"),
        );
        let developer_public_key =
            VerifyingKey::from_public_key_pem(&read_testdata_string!("developer_key.pub.pem"))
                .unwrap();

        let result = report_endorsement(
            endorsement,
            &image_reference,
            &CosignReferenceValues::partial(developer_public_key),
            verification_time,
        );
        assert_that!(result, ok(()));
    }
}

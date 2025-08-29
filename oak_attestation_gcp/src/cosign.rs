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
use oak_proto_rust::oak::attestation::v1::{
    CosignReferenceValues as ProtoCosignReferenceValues, KeyType, SignedEndorsement,
    VerifyingKey as ProtoVerifyingKey,
};
use oak_proto_rust_lib::parse_p256_ecdsa_verifying_key;
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
    #[error("Invalid verifying key: {0}")]
    InvalidVerifyingKey(&'static str),
    #[error("VerifyingKey parsing error: {0}")]
    VerifyingKeyParseError(p256::ecdsa::Error),
    #[error("Unknown error: {0}")]
    UnknownError(&'static str),
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

    pub fn from_proto(proto: &ProtoCosignReferenceValues) -> Result<Self, CosignVerificationError> {
        match &proto.developer_public_key {
            None => Err(CosignVerificationError::MissingEndorsement),
            Some(developer_public_key) => {
                let developer_public_key = parse_verifying_key(developer_public_key.clone())?;
                match &proto.rekor_public_key {
                    None => Ok(Self::partial(developer_public_key)),
                    Some(rekor_public_key) => {
                        let rekor_public_key = parse_verifying_key(rekor_public_key.clone())?;
                        Ok(Self::full(developer_public_key, rekor_public_key))
                    }
                }
            }
        }
    }
}

fn parse_verifying_key(proto: ProtoVerifyingKey) -> Result<VerifyingKey, CosignVerificationError> {
    match proto.r#type() {
        KeyType::EcdsaP256Sha256 => parse_p256_ecdsa_verifying_key(proto)
            .map_err(CosignVerificationError::VerifyingKeyParseError),
        _ => Err(CosignVerificationError::InvalidVerifyingKey(
            "VerifyingKey.type is not EcdsaP256Sha256",
        )),
    }
}

#[derive(Debug)]
pub struct CosignVerificationReport {
    pub statement_verification: Result<StatementReport, CosignVerificationError>,
}

impl CosignVerificationReport {
    pub fn into_checked(self) -> Result<(), CosignVerificationError> {
        match self {
            CosignVerificationReport {
                statement_verification:
                    Ok(StatementReport {
                        statement_validation: Ok(()),
                        rekor_verification: None | Some(Ok(())),
                    }),
            } => Ok(()),
            CosignVerificationReport { statement_verification } => {
                let statement_verification = statement_verification?;
                statement_verification.statement_validation?;
                if let Some(rekor_verification) = statement_verification.rekor_verification {
                    rekor_verification?;
                }
                Err(CosignVerificationError::UnknownError(
                    "CosignVerificationReport verification failed",
                ))
            }
        }
    }
}

#[derive(Debug)]
pub struct StatementReport {
    pub statement_validation: Result<(), CosignVerificationError>,
    pub rekor_verification: Option<Result<(), CosignVerificationError>>,
}

pub fn report_endorsement(
    endorsement: CosignEndorsement,
    image_reference: &Reference,
    ref_values: &CosignReferenceValues,
    verification_time: Instant,
) -> CosignVerificationReport {
    let statement_verification = try {
        let statement = (endorsement.statement)
            .verify(&ref_values.developer_public_key)
            .map_err(CosignVerificationError::StatementVerificationError)?;
        let statement_validation = try {
            let parsed_statement: EndorsementStatement =
                serde_json::from_slice(statement.message())
                    .map_err(CosignVerificationError::StatementParseError)?;

            let subject = image_reference.try_into().map_err(|err: anyhow::Error| {
                CosignVerificationError::ImageReferenceError(err.to_string())
            })?;
            parsed_statement
                .validate(verification_time, &subject, &[])
                .map_err(|err| CosignVerificationError::StatementValidationError(err.to_string()))?
        };

        let rekor_verification = ref_values.rekor_public_key.as_ref().map(|rekor_public_key| {
            if let Some(rekor) = endorsement.rekor {
                try {
                    let rekor = rekor.verify(rekor_public_key).map_err(|err| {
                        CosignVerificationError::RekorError("verifying rekor bundle", err)
                    })?;
                    let rekor: RekorPayload = serde_json::from_slice(rekor.message())
                        .map_err(CosignVerificationError::RekorPayloadParseError)?;
                    let hashed_rekord: HashedRekord<hashedrekord::Unverified> =
                        rekor.payload_body().map_err(|err| {
                            CosignVerificationError::RekorError("parsing hashedrekord payload", err)
                        })?;
                    hashed_rekord
                        .verify(&ref_values.developer_public_key, statement.message())
                        .map_err(|err| {
                            CosignVerificationError::RekorError("verifying rekor payload", err)
                        })?;
                }
            } else {
                Err(CosignVerificationError::MissingEndorsement)
            }
        });

        StatementReport { statement_validation, rekor_verification }
    };

    CosignVerificationReport { statement_verification }
}

#[cfg(test)]
mod tests {
    use core::assert_matches::assert_matches;

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
        assert_matches!(
            result,
            CosignVerificationReport {
                statement_verification: Ok(StatementReport {
                    statement_validation: Ok(()),
                    rekor_verification: None
                })
            }
        );
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
        assert_matches!(result, CosignVerificationReport { statement_verification: Err(_) });
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
        assert_matches!(
            result,
            CosignVerificationReport {
                statement_verification: Ok(StatementReport {
                    statement_validation: Ok(()),
                    rekor_verification: None
                })
            }
        );
    }
}

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

// Provides convenient access to endorsement test data.

use std::fs;

use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{
    ClaimReferenceValue, Endorsement, EndorsementReferenceValue, KeyType, Signature,
    SignedEndorsement, TransparentReleaseEndorsement, VerifyingKey, VerifyingKeyReferenceValue,
    VerifyingKeySet, endorsement::Format,
};
use oak_time::{Instant, make_instant};
use p256::pkcs8::Document;

const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";
const SIGNATURE_PATH: &str = "oak_attestation_verification/testdata/endorsement.json.sig";
const ENDORSER_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/endorser_public_key.pem";
const LOG_ENTRY_PATH: &str = "oak_attestation_verification/testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded
// from https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

const KEY_ID: u32 = 4711;

const PUBLIC_KEY_PEM_LABEL: &str = "PUBLIC KEY";

pub struct EndorsementData {
    // Direct access to data, needed for legacy endorsement verification.
    //
    // TODO: b/379268663 - Stop populating the old-style fields endorser_public_key
    //                     and rekor_public_key.
    pub endorsement: Vec<u8>,
    pub signature: Vec<u8>,
    pub log_entry: Vec<u8>,
    pub rekor_public_key_pem: String,
    pub endorser_public_key: Vec<u8>,
    pub rekor_public_key: Vec<u8>,

    // Valid populated protos, for verify_endorsement().
    pub valid_not_before: Instant,
    pub valid_not_after: Instant,
    pub signed_endorsement: SignedEndorsement,
    pub ref_value: EndorsementReferenceValue,

    // Legacy endorsement.
    pub tr_endorsement: TransparentReleaseEndorsement,
}

impl EndorsementData {
    pub fn load() -> EndorsementData {
        let serialized = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
        let signature = fs::read(data_path(SIGNATURE_PATH)).expect("couldn't read signature");
        let log_entry = fs::read(data_path(LOG_ENTRY_PATH)).expect("couldn't read log entry");
        let endorser_public_key_pem = fs::read_to_string(data_path(ENDORSER_PUBLIC_KEY_PATH))
            .expect("couldn't read endorser public key");
        let rekor_public_key_pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
            .expect("couldn't read rekor public key");

        let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
            .expect("failed to convert endorser key");
        let rekor_public_key =
            convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

        let endorsement = Endorsement {
            format: Format::EndorsementFormatJsonIntoto.into(),
            serialized: serialized.clone(),
            ..Default::default()
        };
        let endorser_key = VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: KEY_ID,
            raw: endorser_public_key.clone(),
        };
        let rekor_key = VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: 0,
            raw: rekor_public_key.clone(),
        };

        EndorsementData {
            endorsement: serialized.clone(),
            signature: signature.clone(),
            log_entry: log_entry.clone(),
            rekor_public_key_pem,
            endorser_public_key,
            rekor_public_key,

            valid_not_before: make_instant!("2024-02-28T09:47:12.067000Z"),
            valid_not_after: make_instant!("2025-02-27T09:47:12.067000Z"),
            signed_endorsement: SignedEndorsement {
                endorsement: Some(endorsement),
                signature: Some(Signature { key_id: KEY_ID, raw: signature.clone() }),
                rekor_log_entry: log_entry.clone(),
            },
            ref_value: EndorsementReferenceValue {
                endorser: Some(VerifyingKeySet {
                    keys: [endorser_key].to_vec(),
                    ..Default::default()
                }),
                required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
                rekor: Some(VerifyingKeyReferenceValue {
                    r#type: Some(
                        oak_proto_rust::oak::attestation::v1::verifying_key_reference_value::Type::Verify(
                            VerifyingKeySet { keys: [rekor_key].to_vec(), ..Default::default() },
                        ),
                    ),
                }),
                ..Default::default()
            },

            tr_endorsement: TransparentReleaseEndorsement {
                endorsement: serialized.clone(),
                subject: vec![],
                endorsement_signature: signature.clone(),
                rekor_log_entry: log_entry.clone(),
            },
        }
    }

    pub fn make_valid_time(&self) -> Instant {
        self.valid_not_before + (self.valid_not_after - self.valid_not_before) / 2
    }
}

/// Converts a PEM public key to raw ASN.1 DER bytes.
fn convert_pem_to_raw(public_key_pem: &str) -> anyhow::Result<Vec<u8>> {
    let (label, key) = Document::from_pem(public_key_pem)
        .map_err(|e| anyhow::anyhow!("Couldn't interpret PEM: {e}"))?;

    anyhow::ensure!(
        label == PUBLIC_KEY_PEM_LABEL,
        "PEM label {label} is not {PUBLIC_KEY_PEM_LABEL}"
    );

    Ok(key.into_vec())
}

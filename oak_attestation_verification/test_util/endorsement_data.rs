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

use hex;
use key_util::convert_pem_to_raw;
use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{
    ClaimReferenceValue, Endorsement, EndorsementReferenceValue, KeyType, PesReferenceValue,
    Signature, SignedEndorsement, TLogReferenceValues, TransparentReleaseEndorsement, VerifyingKey,
    VerifyingKeySet, endorsement::Format,
};
use oak_time::{Instant, make_instant};
use prost::Message;

const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";
const SIGNATURE_PATH: &str = "oak_attestation_verification/testdata/endorsement.json.sig";
const ENDORSER_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/endorser_public_key.pem";
const LOG_ENTRY_PATH: &str = "oak_attestation_verification/testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded
// from https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

// Specific test data for PES Sunny Day integration test.
const PES_SERVICE_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/pes/pes_public_key.pem";
// Data that is provided to PES by TR
const PES_ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/pes/endorsement.json";
// A signature of data that is provided to PES by TR
const PES_ENDORSER_SIGNATURE_PATH: &str =
    "oak_attestation_verification/testdata/pes/endorser_signature.sig";
// Key that was used to sign data provided by TR
const PES_ENDORSER_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/pes/endorser_public_key.pem";
const PES_SERVICE_SIGNATURE_HEX_PATH: &str =
    "oak_attestation_verification/testdata/pes/pes_signature.hex";
const PES_TLOG_RECEIPT_BINARY_PATH: &str =
    "oak_attestation_verification/testdata/pes/tlog_receipt.binarypb";

const KEY_ID: u32 = 4711;

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
    pub pes_public_key: Vec<u8>,

    // Valid populated protos, for verify_endorsement().
    pub valid_not_before: Instant,
    pub valid_not_after: Instant,
    pub signed_endorsement: SignedEndorsement,
    pub ref_value: EndorsementReferenceValue,

    // Legacy endorsement.
    pub tr_endorsement: TransparentReleaseEndorsement,
}

impl EndorsementData {
    #[allow(deprecated)]
    pub fn load_for_rekor_verification() -> EndorsementData {
        let serialized = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
        let signature = fs::read(data_path(SIGNATURE_PATH)).expect("couldn't read signature");
        let log_entry = fs::read(data_path(LOG_ENTRY_PATH)).expect("couldn't read log entry");
        let endorser_public_key_pem = fs::read_to_string(data_path(ENDORSER_PUBLIC_KEY_PATH))
            .expect("couldn't read endorser public key");
        let rekor_public_key_pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
            .expect("couldn't read rekor public key");
        let pes_public_key_pem = fs::read_to_string(data_path(PES_SERVICE_PUBLIC_KEY_PATH))
            .expect("couldn't read PES public key");

        let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
            .expect("failed to convert endorser key");
        let rekor_public_key =
            convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");
        let pes_public_key =
            convert_pem_to_raw(&pes_public_key_pem).expect("failed to convert PES key");

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
            pes_public_key,

            valid_not_before: make_instant!("2024-02-28T09:47:12.067000Z"),
            valid_not_after: make_instant!("2025-02-27T09:47:12.067000Z"),
            signed_endorsement: SignedEndorsement {
                endorsement: Some(endorsement),
                signature: Some(Signature { key_id: KEY_ID, raw: signature.clone() }),
                rekor_log_entry: log_entry.clone(),
                c2sp_tlog_proof: vec![],
                pes_confirmation: vec![],
            },
            ref_value: EndorsementReferenceValue {
                endorser: Some(VerifyingKeySet {
                    keys: [endorser_key].to_vec(),
                    ..Default::default()
                }),
                required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
                tlog: Some(TLogReferenceValues {
                    strategy: Some(
                        oak_proto_rust::oak::attestation::v1::t_log_reference_values::Strategy::All(
                            (),
                        ),
                    ),
                    rekor: Some(VerifyingKeySet {
                        keys: [rekor_key].to_vec(),
                        ..Default::default()
                    }),
                    ..Default::default()
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

    #[allow(deprecated)]
    pub fn load_for_pes_verification() -> EndorsementData {
        // 1. The Core Data (The Endorsement)
        let serialized_endorsement =
            fs::read(data_path(PES_ENDORSEMENT_PATH)).expect("couldn't read endorsement");

        // 2. The Endorser (Oak TR Process)
        let endorser_signature =
            fs::read(data_path(PES_ENDORSER_SIGNATURE_PATH)).expect("couldn't read signature");
        let endorser_public_key_pem = fs::read_to_string(data_path(PES_ENDORSER_PUBLIC_KEY_PATH))
            .expect("couldn't read endorser public key");
        let endorser_public_key_raw = convert_pem_to_raw(endorser_public_key_pem.as_str())
            .expect("failed to convert endorser key");

        // 3. The Notary (PES Service)
        let pes_signature_hex = fs::read_to_string(data_path(PES_SERVICE_SIGNATURE_HEX_PATH))
            .expect("couldn't read RSA signature hex");
        let service_signature =
            hex::decode(pes_signature_hex.trim()).expect("failed to decode PES signature hex");

        let service_public_key_pem = fs::read_to_string(data_path(PES_SERVICE_PUBLIC_KEY_PATH))
            .expect("couldn't read PES public key");
        let service_public_key_raw =
            convert_pem_to_raw(&service_public_key_pem).expect("failed to convert PES key");

        let tlog_receipt_bytes = fs::read(data_path(PES_TLOG_RECEIPT_BINARY_PATH))
            .expect("couldn't read PES TLog receipt binary");
        let tlog_receipt =
            oak_proto_rust::google::pes::v1::TLogReceipt::decode(&*tlog_receipt_bytes)
                .expect("couldn't decode TLogReceipt");

        let endorsement_proto = Endorsement {
            format: Format::EndorsementFormatJsonIntoto.into(),
            serialized: serialized_endorsement.clone(),
            ..Default::default()
        };
        let endorser_verifying_key = VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: KEY_ID,
            raw: endorser_public_key_raw.clone(),
        };
        let service_verifying_key = VerifyingKey {
            r#type: KeyType::RsaSha2256.into(),
            key_id: 0,
            raw: service_public_key_raw.clone(),
        };

        let public_endorsement = oak_proto_rust::google::pes::v1::PublicEndorsement {
            name: "endorsements/test".to_string(),
            statement: Some(oak_proto_rust::google::pes::v1::Statement {
                format: oak_proto_rust::google::pes::v1::statement::Format::JsonIntoto.into(),
                serialized: serialized_endorsement.clone(),
            }),
            statement_signature: Some(oak_proto_rust::google::pes::v1::Signature {
                // The endorsement is signed by the Oak Endorser (Endorser).
                signature: endorser_signature.clone(),
                verification_material: Some(oak_proto_rust::google::pes::v1::VerificationMaterial {
                    verification_material: Some(
                        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::EcdsaP256Sha256(
                            oak_proto_rust::google::pes::v1::EcdsaP256PublicKey {
                                der_bytes: endorser_public_key_raw.clone(),
                            }
                        )
                    ),
                }),
            }),
            endorsement_signatures: vec![oak_proto_rust::google::pes::v1::Signature {
                // The PES Confirmation is signed by PES.
                signature: service_signature.clone(),
                verification_material: Some(oak_proto_rust::google::pes::v1::VerificationMaterial {
                    verification_material: Some(
                        oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial::X509Certificate(
                            oak_proto_rust::google::pes::v1::X509Der {
                                der_bytes: service_public_key_raw.clone(),
                            }
                        )
                    ),
                }),
            }],
            tlog_receipt: Some(tlog_receipt),
        };
        use base64::{Engine, engine::general_purpose::STANDARD};
        use oak_proto_rust::google::pes::v1::verification_material::VerificationMaterial as VmOneof;

        let pes_confirmation_json = serde_json::json!({
            "name": public_endorsement.name,
            "statement": {
                "serialized": STANDARD.encode(public_endorsement.statement.as_ref().unwrap().serialized.as_slice()),
                "format": "JSON_INTOTO",
            },
            "statementSignature": {
                "signature": STANDARD.encode(public_endorsement.statement_signature.as_ref().unwrap().signature.as_slice()),
                "verificationMaterial": {
                    "ecdsaP256Sha256": {
                        "derBytes": STANDARD.encode(match public_endorsement.statement_signature.as_ref().unwrap().verification_material.as_ref().unwrap().verification_material.as_ref().unwrap() {
                            VmOneof::EcdsaP256Sha256(key) => &key.der_bytes,
                            _ => panic!("unexpected VM"),
                        }),
                    }
                }
            },
            "endorsementSignatures": [
                {
                    "signature": STANDARD.encode(public_endorsement.endorsement_signatures[0].signature.as_slice()),
                    "verificationMaterial": {
                        "x509Certificate": {
                            "derBytes": STANDARD.encode(match public_endorsement.endorsement_signatures[0].verification_material.as_ref().unwrap().verification_material.as_ref().unwrap() {
                                VmOneof::X509Certificate(cert) => &cert.der_bytes,
                                _ => panic!("unexpected VM"),
                            }),
                        }
                    }
                }
            ],
            "tlogReceipt": {
                "entryId": public_endorsement.tlog_receipt.as_ref().unwrap().entry_id,
            }
        });
        let pes_confirmation =
            serde_json::to_vec(&pes_confirmation_json).expect("failed to encode JSON");

        EndorsementData {
            endorsement: serialized_endorsement.clone(),
            signature: endorser_signature.clone(),
            log_entry: vec![],
            rekor_public_key_pem: "".to_string(),
            endorser_public_key: endorser_public_key_raw,
            rekor_public_key: vec![],
            pes_public_key: service_public_key_raw,

            valid_not_before: make_instant!("2024-02-28T09:47:12.067000Z"),
            valid_not_after: make_instant!("2025-02-27T09:47:12.067000Z"),
            signed_endorsement: SignedEndorsement {
                endorsement: Some(endorsement_proto),
                signature: Some(Signature { key_id: KEY_ID, raw: endorser_signature.clone() }),
                rekor_log_entry: vec![],
                c2sp_tlog_proof: vec![],
                pes_confirmation,
            },
            ref_value: EndorsementReferenceValue {
                endorser: Some(VerifyingKeySet {
                    keys: [endorser_verifying_key].to_vec(),
                    ..Default::default()
                }),
                required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
                tlog: Some(TLogReferenceValues {
                    strategy: Some(
                        oak_proto_rust::oak::attestation::v1::t_log_reference_values::Strategy::All(
                            (),
                        ),
                    ),
                    pes: Some(PesReferenceValue {
                        key_set: Some(VerifyingKeySet {
                            keys: [service_verifying_key].to_vec(),
                            ..Default::default()
                        }),
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            },

            tr_endorsement: TransparentReleaseEndorsement {
                endorsement: serialized_endorsement.clone(),
                subject: vec![],
                endorsement_signature: endorser_signature.clone(),
                rekor_log_entry: vec![],
            },
        }
    }

    pub fn make_valid_time(&self) -> Instant {
        self.valid_not_before + (self.valid_not_after - self.valid_not_before) / 2
    }
}

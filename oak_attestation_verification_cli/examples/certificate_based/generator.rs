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

//! This binary generates a `CollectedAttestation` and a
//! `ReferenceValuesCollection` for testing the Attestation Verification CLI
//! with certificate-based attestation. These are written out to files as
//! binary-encoded protobufs.

use std::{collections::BTreeMap, fs::File, io::Write, path::PathBuf};

use chrono::Utc;
use clap::Parser;
use cxx_string::CxxString;
use oak_ffi_bytes::BytesView;
use oak_proto_rust::{
    attestation::CERTIFICATE_BASED_ATTESTATION_ID,
    certificate::SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
    oak::{
        attestation::v1::{
            collected_attestation::RequestMetadata, reference_values,
            CertificateAuthorityEndorsement, CertificateAuthorityReferenceValue,
            CertificateBasedReferenceValues, CollectedAttestation, Endorsements, Event, EventLog,
            Evidence, ReferenceValues, ReferenceValuesCollection, SessionBindingPublicKeyData,
            SessionBindingPublicKeyEndorsement,
        },
        crypto::v1::{
            Certificate, CertificatePayload, SignatureInfo, SubjectPublicKeyInfo, Validity,
        },
        session::v1::{EndorsedEvidence, SessionBinding},
    },
};
use oak_time::{Duration, Instant};
use p256::ecdsa::{signature::Signer, Signature, SigningKey, VerifyingKey};
use prost::Message;

#[derive(Parser, Debug)]
struct Flags {
    #[arg(long)]
    collected_attestation_out: PathBuf,
    #[arg(long)]
    reference_values_out: PathBuf,
}

const HANDSHAKE: &str = "handshake!";

fn main() -> anyhow::Result<()> {
    let Flags { collected_attestation_out, reference_values_out } = Flags::parse();

    let now = Utc::now();

    // Generate session binding keypair.
    let signing_key = SigningKey::random(&mut rand_core::OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);

    // Create certificate payload containing the session binding public key.
    let certificate_payload = CertificatePayload {
        validity: Some(Validity {
            not_before: Some((Instant::from(now) - Duration::from_seconds(60)).into_timestamp()),
            not_after: Some((Instant::from(now) + Duration::from_seconds(60)).into_timestamp()),
        }),
        subject_public_key_info: Some(SubjectPublicKeyInfo {
            public_key: verifying_key.to_sec1_bytes().to_vec(),
            purpose_id: SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID.to_vec(),
        }),
        proof_of_freshness: None,
    }
    .encode_to_vec();

    // Generate a new CA keypair (with Tink), and use it to sign the
    // CertificatePayload.
    let SignatureWrapper {
        signature: certificate_payload_signature,
        tink_public_keyset: certificate_authority_public_keyset,
    } = sign_with_tink(certificate_payload.as_slice())?;

    // Sign the handshake hash.
    let session_binding_signature: Signature = signing_key.sign(HANDSHAKE.as_bytes());

    // Tie all of the above together into output protobufs.
    let collected_attestation = CollectedAttestation {
        request_metadata: Some(RequestMetadata {
            request_time: Some(Instant::from(now).into_timestamp()),
            uri: "some://where".to_string(),
        }),
        endorsed_evidence: BTreeMap::from([(
            CERTIFICATE_BASED_ATTESTATION_ID.to_string(),
            EndorsedEvidence {
                evidence: Some(evidence(&verifying_key)),
                endorsements: Some(endorsements(
                    certificate_payload,
                    certificate_payload_signature,
                )),
            },
        )]),
        session_bindings: BTreeMap::from([(
            CERTIFICATE_BASED_ATTESTATION_ID.to_string(),
            session_binding(&session_binding_signature),
        )]),
        handshake_hash: HANDSHAKE.as_bytes().to_vec(),
    };

    let reference_values_collection = ReferenceValuesCollection {
        reference_values: BTreeMap::from([(
            CERTIFICATE_BASED_ATTESTATION_ID.to_string(),
            reference_values(certificate_authority_public_keyset),
        )]),
    };

    // Write output files.
    let mut file = File::create(collected_attestation_out)?;
    file.write_all(&collected_attestation.encode_to_vec())?;
    let mut file = File::create(reference_values_out)?;
    file.write_all(&reference_values_collection.encode_to_vec())?;

    Ok(())
}

struct SignatureWrapper {
    signature: Vec<u8>,
    tink_public_keyset: Vec<u8>,
}

const STATUS_OK: i32 = 0;

fn sign_with_tink(message: &[u8]) -> anyhow::Result<SignatureWrapper> {
    let signature_status_wrapper: SignatureStatusWrapper =
        unsafe { SignWithTink(BytesView::new_from_slice(message)) };
    match signature_status_wrapper.status_code {
        STATUS_OK => Ok(SignatureWrapper {
            signature: signature_status_wrapper.signature.as_slice().to_vec(),
            tink_public_keyset: signature_status_wrapper.tink_public_keyset.as_slice().to_vec(),
        }),
        // All other statuses are not OK.
        _ => {
            let error_message_bytes = signature_status_wrapper.status_message.as_slice();
            let error_message = String::from_utf8(error_message_bytes.to_vec())
                .map_err(|_| anyhow::anyhow!("failed to parse the error"))?;
            anyhow::bail!(error_message)
        }
    }
}

fn evidence(verifying_key: &VerifyingKey) -> Evidence {
    Evidence {
        event_log: Some(EventLog {
            encoded_events: vec![Event {
                tag: "session_binding_key".to_string(),
                event: Some(prost_types::Any {
                    type_url: "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                        .to_string(),
                    value: SessionBindingPublicKeyData {
                        session_binding_public_key: verifying_key.to_sec1_bytes().to_vec(),
                    }
                    .encode_to_vec(),
                }),
            }
            .encode_to_vec()],
        }),
        ..Default::default()
    }
}

fn endorsements(
    certificate_payload: Vec<u8>,
    certificate_payload_signature: Vec<u8>,
) -> Endorsements {
    Endorsements {
        events: vec![SessionBindingPublicKeyEndorsement {
            ca_endorsement: Some(CertificateAuthorityEndorsement {
                certificate: Some(Certificate {
                    serialized_payload: certificate_payload,
                    signature_info: Some(SignatureInfo {
                        signature: certificate_payload_signature,
                    }),
                }),
            }),
            ..Default::default()
        }
        .into()],
        ..Default::default()
    }
}

fn session_binding(session_binding_signature: &Signature) -> SessionBinding {
    SessionBinding { binding: session_binding_signature.to_bytes().to_vec() }
}

fn reference_values(tink_proto_keyset: Vec<u8>) -> ReferenceValues {
    ReferenceValues {
        r#type: Some(reference_values::Type::CertificateBased(CertificateBasedReferenceValues {
            ca: Some(CertificateAuthorityReferenceValue { tink_proto_keyset }),
        })),
    }
}

// Mirrors SignatureStatusWrapper in
// cc/crypto/tink/signature/testing/signature-ffi.h
#[repr(C)]
struct SignatureStatusWrapper {
    status_code: i32,
    status_message: CxxString,
    signature: CxxString,
    tink_public_keyset: CxxString,
}

// See the implementation in cc/crypto/tink/signature/testing/signature-ffi.h
#[link(name = "signature-ffi")]
extern "C" {
    fn SignWithTink(message: BytesView) -> SignatureStatusWrapper;
}

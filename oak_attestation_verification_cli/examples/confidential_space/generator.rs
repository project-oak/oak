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

use std::{collections::BTreeMap, fs::File, io::Write, path::PathBuf};

use base64::{Engine, engine::general_purpose::STANDARD};
use clap::Parser;
use intoto::statement::{DefaultStatement, Subject, make_statement, serialize_statement};
use jwt::{
    SignWithKey, SigningAlgorithm, Token,
    algorithm::{AlgorithmType, openssl::PKeyWithDigest},
    token::Signed,
};
use oak_attestation_gcp::{
    OAK_SESSION_NOISE_V1_AUDIENCE,
    jwt::{Claims, Header},
};
use oak_proto_rust::{
    attestation::CONFIDENTIAL_SPACE_ATTESTATION_ID,
    oak::{
        HexDigest,
        attestation::v1::{
            CollectedAttestation, ConfidentialSpaceEndorsement, ConfidentialSpaceReferenceValues,
            CosignReferenceValues, Endorsements, Event, EventLog, Evidence, ReferenceValues,
            ReferenceValuesCollection, SessionBindingPublicKeyData, SignedEndorsement,
            collected_attestation::RequestMetadata,
            confidential_space_reference_values::ContainerImage, reference_values,
        },
        session::v1::{EndorsedEvidence, SessionBinding},
    },
};
use oak_proto_rust_lib::p256_ecdsa_verifying_key_to_proto;
use oak_time::{Duration, Instant};
use openssl::{
    asn1::Asn1Time,
    hash::MessageDigest,
    pkey::{PKey, Private},
    rsa::Rsa,
    x509::X509,
};
use p256::{
    ecdsa::{
        Signature, SigningKey, VerifyingKey,
        signature::{SignatureEncoding, Signer},
    },
    pkcs8::EncodePublicKey,
};
use prost::Message;
use rekor::log_entry::{
    Body, Data, GenericSignature, Hash, LogEntry, PublicKey, Spec, Verification,
};
use serde_json::json;
use sha2::Digest;
use verify_endorsement::create_signed_endorsement;

#[derive(Parser, Debug)]
struct Flags {
    #[arg(long)]
    collected_attestation_out: PathBuf,
    #[arg(long)]
    reference_values_out: PathBuf,
}

const SESSION_TOKEN: &str = "session_token!";
const IMAGE_DIGEST: &str = "173e9531a1306d55c6a5a36f6e57d2291a5b5c4f8e3c8a45d3b89a4d1f1b3a80";

fn main() -> anyhow::Result<()> {
    let Flags { collected_attestation_out, reference_values_out } = Flags::parse();

    let now = oak_time_std::instant::now();

    // Generate a 3-certificate chain. There is no documented specific length on the
    // actual Confidential Space certification chain, this is just here in order to
    // render a final report which includes a chain.
    // 1. A self-signed root certificate.
    let root_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
    let root_cert = issue_self_signed_cert(now, &root_pkey)?;

    // 2. An intermediate certificate signed by the root.
    let intermediate_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
    let intermediate_cert = issue_cert(now, &intermediate_pkey, &root_pkey)?;

    // 3. A leaf certificate signed by the intermediate.
    let leaf_pkey = PKey::from_rsa(Rsa::generate(2048)?)?;
    let leaf_cert = issue_cert(now, &leaf_pkey, &intermediate_pkey)?;

    // Generate session binding keypair.
    let binding_key = SigningKey::random(&mut rand_core::OsRng);
    let binding_verifying_key = binding_key.verifying_key();

    // Create JWT.
    let nonce = {
        let mut hasher = sha2::Sha256::new();
        hasher.update(binding_verifying_key.to_sec1_bytes());
        hex::encode(hasher.finalize())
    };

    let jwt = Token::new(
        Header {
            // https://cloud.google.com/confidential-computing/confidential-vm/docs/token-claims#token_items
            // "Confidential VM supports the RS256 algorithm."
            algorithm: jwt::AlgorithmType::Rs256,
            x509_chain: vec![
                STANDARD.encode(leaf_cert.to_der()?),
                STANDARD.encode(intermediate_cert.to_der()?),
                STANDARD.encode(root_cert.to_der()?),
            ],
        },
        generate_jwt_claims(now, nonce),
    );

    // Sign the JWT.
    let private_key = PKeyWithDigest { digest: MessageDigest::sha256(), key: leaf_pkey };
    let jwt = jwt.sign_with_key(&Rs256PKeyWithDigest { delegate: private_key })?;

    // Create session binding.
    let session_binding_signature: Signature = binding_key.sign(SESSION_TOKEN.as_bytes());

    // Generate workload endorsement.
    let developer_key = SigningKey::random(&mut rand_core::OsRng);
    let rekor_key = SigningKey::random(&mut rand_core::OsRng);

    let serialized_endorsement = serialize_statement(&generate_endorsement_statement(now)?)?;
    let developer_signature: Signature = developer_key.sign(&serialized_endorsement);

    let workload_endorsement = create_signed_endorsement(
        serialized_endorsement.as_slice(),
        developer_signature.to_der().to_vec().as_slice(),
        1,
        &[],
        serde_json::to_vec(&json!({
            "sha256:".to_owned() + IMAGE_DIGEST: generate_log_entry(
                now,
                sha2::Sha256::digest(&serialized_endorsement).to_vec(),
                developer_key.verifying_key(),
                &developer_signature,
                &rekor_key,
            )?
        }))?
        .as_slice(),
    );

    // Create final protobufs.
    let collected_attestation = CollectedAttestation {
        request_metadata: Some(RequestMetadata {
            request_time: Some(now.into_timestamp()),
            uri: "some://where".to_string(),
        }),
        endorsed_evidence: BTreeMap::from([(
            CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
            EndorsedEvidence {
                evidence: Some(generate_evidence(binding_verifying_key)),
                endorsements: Some(generate_endorsements(&jwt, workload_endorsement)),
            },
        )]),
        session_bindings: BTreeMap::from([(
            CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
            SessionBinding { binding: session_binding_signature.to_bytes().to_vec() },
        )]),
        handshake_hash: SESSION_TOKEN.as_bytes().to_vec(),
    };

    let reference_values_collection = ReferenceValuesCollection {
        reference_values: BTreeMap::from([(
            CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
            ReferenceValues {
                r#type: Some(reference_values::Type::ConfidentialSpace(
                    ConfidentialSpaceReferenceValues {
                        root_certificate_pem: String::from_utf8(root_cert.to_pem()?)?,
                        #[allow(deprecated)]
                        container_image: Some(ContainerImage::CosignReferenceValues(
                            CosignReferenceValues {
                                developer_public_key: Some(
                                    p256_ecdsa_verifying_key_to_proto(
                                        developer_key.verifying_key(),
                                    )
                                    .map_err(anyhow::Error::msg)?,
                                ),
                                rekor_public_key: Some(
                                    p256_ecdsa_verifying_key_to_proto(rekor_key.verifying_key())
                                        .map_err(anyhow::Error::msg)?,
                                ),
                            },
                        )),
                    },
                )),
            },
        )]),
    };

    // Write files.
    let mut file = File::create(collected_attestation_out)?;
    file.write_all(&collected_attestation.encode_to_vec())?;
    let mut file = File::create(reference_values_out)?;
    file.write_all(&reference_values_collection.encode_to_vec())?;

    Ok(())
}

fn issue_self_signed_cert(now: Instant, pkey: &PKey<Private>) -> anyhow::Result<X509> {
    issue_cert(now, pkey, pkey)
}

fn issue_cert(
    now: Instant,
    subject_pkey: &PKey<Private>,
    issuer_pkey: &PKey<Private>,
) -> anyhow::Result<X509> {
    Ok({
        let mut builder = X509::builder()?;
        builder.set_pubkey(subject_pkey)?;

        let not_before = Asn1Time::from_unix((now - Duration::from_hours(1)).into_unix_seconds())?;
        builder.set_not_before(&not_before)?;
        let not_after = Asn1Time::from_unix((now + Duration::from_hours(1)).into_unix_seconds())?;
        builder.set_not_after(&not_after)?;

        builder.sign(issuer_pkey, MessageDigest::sha256())?;
        builder.build()
    })
}

fn generate_jwt_claims(now: Instant, nonce: String) -> Claims {
    Claims {
        audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
        eat_nonce: nonce,
        issued_at: now,
        not_before: now - Duration::from_hours(1),
        not_after: now + Duration::from_hours(1),
        submods: oak_attestation_gcp::jwt::Submods {
            confidential_space: oak_attestation_gcp::jwt::ConfidentialSpaceClaims {
                // https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#submods-claims
                support_attributes: vec!["STABLE".to_string()],
            },
            container: oak_attestation_gcp::jwt::ContainerClaims {
                image_reference: "gcr.io/oak-ci/oak-containers-system-image".to_string(),
                image_digest: "sha256:".to_owned() + IMAGE_DIGEST,
                ..Default::default()
            },
        },
        // See 'dbgstat' in https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#top-level_claims.
        debug_status: "disabled-since-boot".to_string(),
        // See 'swname' in https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims#top-level_claims.
        software_name: "CONFIDENTIAL_SPACE".to_string(),
        ..Default::default()
    }
}

fn generate_endorsement_statement(now: Instant) -> anyhow::Result<DefaultStatement> {
    let mut endorsement_statement = make_statement(
        "gcr.io/oak-ci/oak-containers-system-image",
        &HexDigest { sha2_256: IMAGE_DIGEST.to_string(), ..Default::default() },
        now,
        now - Duration::from_hours(1),
        now + Duration::from_hours(1),
        vec![],
    );
    // TODO: b/443012225 - remove this hack once trex treats "sha256" and "sha2_256"
    // as equivalent.
    endorsement_statement.subject = vec![Subject {
        name: "gcr.io/oak-ci/oak-containers-system-image".to_string(),
        digest: BTreeMap::from([("sha256".to_string(), IMAGE_DIGEST.to_string())]),
    }];
    Ok(endorsement_statement)
}

fn generate_log_entry(
    now: Instant,
    digest: Vec<u8>,
    public_key: &VerifyingKey,
    signature: &Signature,
    rekor_key: &SigningKey,
) -> anyhow::Result<LogEntry> {
    let mut log_entry = LogEntry {
        body: STANDARD.encode(serde_json::to_vec(&Body {
            api_version: "0.0.1".to_string(),
            kind: "hashedrekord".to_string(),
            spec: Spec {
                data: Data {
                    hash: Hash { algorithm: "sha256".to_string(), value: hex::encode(digest) },
                },
                signature: GenericSignature {
                    content: STANDARD.encode(signature.to_der()),
                    public_key: PublicKey {
                        content: STANDARD.encode(
                            public_key
                                .to_public_key_pem(Default::default())
                                .map_err(anyhow::Error::msg)?,
                        ),
                    },
                },
            },
        })?),
        integrated_time: now.into_unix_seconds() as usize,
        log_id: "log_id".to_string(),
        log_index: 456,
        verification: None,
    };
    let rekor_signature: Signature = rekor_key.sign(&serde_json::to_vec(&log_entry)?);
    log_entry.verification =
        Some(Verification { signed_entry_timestamp: STANDARD.encode(rekor_signature.to_der()) });
    Ok(log_entry)
}

fn generate_evidence(session_binding_public_key: &VerifyingKey) -> Evidence {
    Evidence {
        event_log: Some(EventLog {
            encoded_events: vec![
                Event {
                    tag: "session_binding_key".to_string(),
                    event: Some(prost_types::Any {
                        type_url:
                            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                                .to_string(),
                        value: SessionBindingPublicKeyData {
                            session_binding_public_key: session_binding_public_key
                                .to_sec1_bytes()
                                .to_vec(),
                        }
                        .encode_to_vec(),
                    }),
                }
                .encode_to_vec(),
            ],
        }),
        ..Default::default()
    }
}

fn generate_endorsements(
    jwt: &Token<Header, Claims, Signed>,
    workload_endorsement: SignedEndorsement,
) -> Endorsements {
    Endorsements {
        events: vec![
            ConfidentialSpaceEndorsement {
                jwt_token: jwt.as_str().to_string(),
                workload_endorsement: Some(workload_endorsement),
            }
            .into(),
        ],
        ..Default::default()
    }
}

// This is a hack copied from `report.rs` to work around an issue with the jwt
// crate.
struct Rs256PKeyWithDigest<T> {
    delegate: PKeyWithDigest<T>,
}

impl SigningAlgorithm for Rs256PKeyWithDigest<openssl::pkey::Private> {
    fn algorithm_type(&self) -> AlgorithmType {
        AlgorithmType::Rs256
    }
    fn sign(&self, header: &str, claims: &str) -> Result<String, jwt::error::Error> {
        self.delegate.sign(header, claims)
    }
}

//
// Copyright 2023 The Project Oak Authors
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

//! This crate contains the logic used by stage0 to create attestations. It is
//! broken out into a seperate crate to allow this logic to be used
//! independently used in tests to create mock attestations, without also
//! pulling in the global allocator and attestation hardware attestation
//! retrieval logic of the stage0 crate.

#![no_std]

extern crate alloc;

use alloc::{string::String, vec, vec::Vec};

use coset::{cbor::value::Value, cwt::ClaimName, CborSerializable, CoseSign1};
use hkdf::Hkdf;
use oak_dice::{
    cert::{
        derive_verifying_key_id, generate_ecdsa_key_pair, generate_signing_certificate,
        verifying_key_to_cose_key, ACPI_MEASUREMENT_ID, EVENT_ID, INITRD_MEASUREMENT_ID,
        KERNEL_COMMANDLINE_ID, KERNEL_COMMANDLINE_MEASUREMENT_ID, KERNEL_LAYER_ID,
        KERNEL_MEASUREMENT_ID, MEMORY_MAP_MEASUREMENT_ID, SETUP_DATA_MEASUREMENT_ID, SHA2_256_ID,
    },
    evidence::{Stage0DiceData, TeePlatform, STAGE0_MAGIC},
};
use oak_proto_rust::oak::attestation::v1::{
    CertificateAuthority, DiceData, EventLog, Evidence, LayerEvidence, RootLayerEvidence,
};
use oak_sev_snp_attestation_report::{AttestationReport, REPORT_DATA_SIZE};
use p256::ecdsa::SigningKey;
use prost::Message;
use sha2::{Digest, Sha256};
use zerocopy::{AsBytes, FromZeroes};

use crate::alloc::string::ToString;

pub type DerivedKey = [u8; 32];

/// Generates an ECA certificate for use by the next boot stage (Stage 1).
fn generate_stage1_certificate(
    stage0_eca_key: &SigningKey,
    stage0_cert_issuer: String,
    encoded_stage0_event: &[u8],
) -> (CoseSign1, SigningKey) {
    // Generate additional claims to cover the measurements.
    let additional_claims = {
        let measurements = decode_stage0_event(encoded_stage0_event);
        vec![
            (
                ClaimName::PrivateUse(KERNEL_LAYER_ID),
                Value::Map(vec![
                    (
                        Value::Integer(KERNEL_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(
                                shorten_cmdline(&measurements.kernel_cmdline).as_bytes().into()
                            ),
                        )]),
                    ),
                    (
                        Value::Integer(KERNEL_COMMANDLINE_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(
                                Sha256::digest(measurements.kernel_cmdline.as_bytes()).to_vec()
                            ),
                        )]),
                    ),
                    (
                        Value::Integer(KERNEL_COMMANDLINE_ID.into()),
                        Value::Text(measurements.kernel_cmdline),
                    ),
                    (
                        Value::Integer(SETUP_DATA_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(measurements.setup_data_digest),
                        )]),
                    ),
                    (
                        Value::Integer(INITRD_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(measurements.ram_disk_digest),
                        )]),
                    ),
                    (
                        Value::Integer(MEMORY_MAP_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(measurements.memory_map_digest),
                        )]),
                    ),
                    (
                        Value::Integer(ACPI_MEASUREMENT_ID.into()),
                        Value::Map(alloc::vec![(
                            Value::Integer(SHA2_256_ID.into()),
                            Value::Bytes(measurements.acpi_digest),
                        )]),
                    ),
                ]),
            ),
            (
                ClaimName::PrivateUse(EVENT_ID),
                Value::Map(alloc::vec![(
                    Value::Integer(SHA2_256_ID.into()),
                    Value::Bytes(Sha256::digest(encoded_stage0_event).to_vec()),
                )]),
            ),
        ]
    };

    let (signing_key, verifying_key) = generate_ecdsa_key_pair();
    (
        generate_signing_certificate(
            stage0_eca_key,
            stage0_cert_issuer,
            &verifying_key,
            additional_claims,
        )
        .expect("couldn't generate ECA certificate"),
        signing_key,
    )
}

// TODO: b/331252282 - Remove temporary workaround for cmd line length.
fn shorten_cmdline(cmdline: &str) -> String {
    let max_length: usize = 256;
    if cmdline.len() > max_length { cmdline[..max_length].to_string() } else { cmdline.to_string() }
}

fn decode_stage0_event(
    encoded_event: &[u8],
) -> oak_proto_rust::oak::attestation::v1::Stage0Measurements {
    let decoded_event: oak_proto_rust::oak::attestation::v1::Event =
        Message::decode(encoded_event).expect("Failed to decode stage0 event");

    Message::decode(decoded_event.event.unwrap().value.as_slice())
        .expect("Failed to decode stage0 measurements")
}

/// Generates attestation evidence for the 'measurements' of all Stage 1
/// components.
pub fn generate_dice_data<
    F: FnOnce([u8; REPORT_DATA_SIZE]) -> Result<AttestationReport, &'static str>,
    G: FnOnce() -> Result<DerivedKey, &'static str>,
>(
    get_attestation: F,
    get_derived_key: G,
    tee_platform: TeePlatform,
    encoded_stage0_event: &[u8],
) -> (Stage0DiceData, DiceData) {
    let mut result = Stage0DiceData::new_zeroed();
    // Generate ECA Stage0 key pair. This key will be used to sign Stage1 ECA
    // certificate.
    let (stage0_eca_key, stage0_eca_verifying_key) = generate_ecdsa_key_pair();

    let (stage1_eca_cert, stage1_eca_signing_key) = generate_stage1_certificate(
        &stage0_eca_key,
        hex::encode(derive_verifying_key_id(&stage0_eca_verifying_key)),
        encoded_stage0_event,
    );

    let stage0_eca_verifying_key = verifying_key_to_cose_key(&stage0_eca_verifying_key)
        .to_vec()
        .expect("couldn't serialize the ECA public key");

    let stage1_eca_cert =
        stage1_eca_cert.to_vec().expect("couldn't serialize stage 1 ECA certificate");

    // Use the SHA2-256 digest of the serialized ECA verifying key as the report
    // data.
    let eca_sha2_256_digest = {
        let mut digest = Sha256::default();
        digest.update(&stage0_eca_verifying_key);
        digest.finalize()
    };

    let mut report_data = [0u8; REPORT_DATA_SIZE];
    report_data[..eca_sha2_256_digest.len()].copy_from_slice(&eca_sha2_256_digest[..]);

    let report = get_attestation(report_data).expect("couldn't get attestation report.");
    let report_bytes = report.as_bytes();

    // Use the root derived key as the UDS (unique device secret) for deriving
    // sealing keys.
    let ikm: DerivedKey = get_derived_key().expect("couldn't get derived key");

    // Mix in the measurements of the kernel, the kernel command-line, the kernel
    // setup data and the initial RAM disk when deriving the CDI for Layer 1.
    let salt: Vec<u8> = {
        let measurements = decode_stage0_event(encoded_stage0_event);
        let mut salt = Vec::with_capacity(128);
        salt.extend_from_slice(&measurements.kernel_measurement);
        salt.extend_from_slice(shorten_cmdline(&measurements.kernel_cmdline).as_bytes());
        salt.extend_from_slice(&measurements.setup_data_digest);
        salt.extend_from_slice(&measurements.ram_disk_digest);
        salt
    };
    let hkdf = Hkdf::<Sha256>::new(Some(&salt), &ikm[..]);

    let event_log = {
        let mut base = oak_proto_rust::oak::attestation::v1::EventLog::default();
        base.encoded_events.push(encoded_stage0_event.to_vec());
        base
    };
    let result_evidence = Evidence {
        root_layer: Some(RootLayerEvidence {
            remote_attestation_report: report_bytes.to_vec(),
            eca_public_key: stage0_eca_verifying_key.to_vec(),
            platform: tee_platform as i32,
        }),
        layers: vec![LayerEvidence { eca_certificate: stage1_eca_cert.clone() }],
        application_keys: None,
        event_log: Some(event_log),
    };

    let result_ca =
        CertificateAuthority { eca_private_key: stage1_eca_signing_key.to_bytes().to_vec() };

    let result_dice_data =
        DiceData { evidence: Some(result_evidence), certificate_authority: Some(result_ca) };

    result.magic = STAGE0_MAGIC;
    result.root_layer_evidence.tee_platform = tee_platform as u64;
    result
        .root_layer_evidence
        .set_remote_attestation_report(report_bytes)
        .expect("failed to set remote attestation report");
    result
        .root_layer_evidence
        .set_eca_public_key(&stage0_eca_verifying_key)
        .expect("failed to set eca public key");
    result.layer_1_evidence.eca_certificate[..stage1_eca_cert.len()]
        .copy_from_slice(&stage1_eca_cert);
    result.layer_1_certificate_authority.eca_private_key[..stage1_eca_signing_key.to_bytes().len()]
        .copy_from_slice(stage1_eca_signing_key.to_bytes().as_slice());
    hkdf.expand(b"CDI_Seal", &mut result.layer_1_cdi.cdi[..])
        .expect("invalid length for HKDF output");

    (result, result_dice_data)
}

/// Returns an attestation report.
///
/// Generates an empty attestation report for testing. The additional data will
/// be set bind the DICE chain to the attestation report.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This
///   is typically used to bind information (such as the hash of a public key)
///   to the report.
pub fn mock_attestation_report(
    report_data: [u8; REPORT_DATA_SIZE],
) -> Result<AttestationReport, &'static str> {
    Ok(AttestationReport::from_report_data(report_data))
}

/// Returns a fixed key filled with zeros.
pub fn mock_derived_key() -> Result<DerivedKey, &'static str> {
    Ok(DerivedKey::default())
}

pub fn encoded_stage0_event(
    measurements: oak_proto_rust::oak::attestation::v1::Stage0Measurements,
) -> Vec<u8> {
    let tag = String::from("Stage0");
    let any = prost_types::Any::from_msg(&measurements);
    let event = oak_proto_rust::oak::attestation::v1::Event { tag, event: Some(any.unwrap()) };
    event.encode_to_vec()
}

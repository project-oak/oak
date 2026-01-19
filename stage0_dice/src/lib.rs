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

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

use coset::CborSerializable;
use hkdf::Hkdf;
use oak_dice::{
    cert::{generate_ecdsa_key_pair, verifying_key_to_cose_key},
    evidence::{Stage0DiceData, TeePlatform, STAGE0_MAGIC},
};
use oak_proto_rust::oak::attestation::v1::{
    CertificateAuthority, DiceData, Evidence, RootLayerEvidence,
};
use oak_sev_snp_attestation_report::{AttestationReport, REPORT_DATA_SIZE};
use prost::Message;
use sha2::{Digest, Sha256};
use zerocopy::{FromZeros, IntoBytes};

pub type DerivedKey = [u8; 32];

const STAGE0_TAG: &str = "Stage0";
const STAGE0_TRANSPARENT_TAG: &str = "Stage0Transparent";

// TODO: b/331252282 - Remove temporary workaround for cmd line length.
fn shorten_cmdline(cmdline: &str) -> String {
    let max_length: usize = 256;
    if cmdline.len() > max_length {
        cmdline[..max_length].to_string()
    } else {
        cmdline.to_string()
    }
}

pub fn dice_data_proto_to_stage0_dice_data(
    attestation_data: &DiceData,
) -> Result<Stage0DiceData, &'static str> {
    let mut result = Stage0DiceData::new_zeroed();
    let evidence = attestation_data.evidence.as_ref().ok_or("no evidence")?;
    result.magic = STAGE0_MAGIC;
    if let Some(root_layer) = evidence.root_layer.as_ref() {
        result.root_layer_evidence.tee_platform = root_layer.platform as u64;
        result
            .root_layer_evidence
            .set_remote_attestation_report(root_layer.remote_attestation_report.as_slice())?;
        result.root_layer_evidence.set_eca_public_key(root_layer.eca_public_key.as_slice())?;
    }
    if let Some(first_layer) = &evidence.layers.first() {
        let stage1_eca_cert = first_layer.eca_certificate.as_slice();
        result.layer_1_evidence.eca_certificate[..stage1_eca_cert.len()]
            .copy_from_slice(stage1_eca_cert);
    }
    if let Some(certificate_authority) = attestation_data.certificate_authority.as_ref() {
        let eca_private_key = certificate_authority.eca_private_key.as_slice();
        result.layer_1_certificate_authority.eca_private_key[..eca_private_key.len()]
            .copy_from_slice(eca_private_key);
    }
    Ok(result)
}

/// Generates the initial DICE data that can be used as the starting state for a
/// DICE attester.
pub fn generate_initial_dice_data<
    F: FnOnce([u8; REPORT_DATA_SIZE]) -> Result<AttestationReport, &'static str>,
>(
    get_attestation: F,
    tee_platform: TeePlatform,
) -> Result<DiceData, &'static str> {
    // Generate ECA Stage0 key pair. This key will be used to sign Stage1 ECA
    // certificate.
    let (stage0_eca_key, stage0_eca_verifying_key) = generate_ecdsa_key_pair();
    let stage0_eca_verifying_key = verifying_key_to_cose_key(&stage0_eca_verifying_key)
        .to_vec()
        .map_err(|_| "couldn't serialize the ECA public key")?;

    // Use the SHA2-256 digest of the serialized ECA verifying key as the report
    // data.
    let eca_sha2_256_digest = {
        let mut digest = Sha256::default();
        digest.update(&stage0_eca_verifying_key);
        digest.finalize()
    };

    let mut report_data = [0u8; REPORT_DATA_SIZE];
    report_data[..eca_sha2_256_digest.len()].copy_from_slice(&eca_sha2_256_digest[..]);

    let report = get_attestation(report_data)?;
    let report_bytes = report.as_bytes();

    let event_log = oak_proto_rust::oak::attestation::v1::EventLog::default();

    let result_evidence = Evidence {
        root_layer: Some(RootLayerEvidence {
            remote_attestation_report: report_bytes.to_vec(),
            eca_public_key: stage0_eca_verifying_key.to_vec(),
            platform: tee_platform as i32,
        }),
        layers: Vec::new(),
        application_keys: None,
        event_log: Some(event_log),
        transparent_event_log: None,
        signed_user_data_certificate: Vec::new(),
    };

    let result_ca = CertificateAuthority { eca_private_key: stage0_eca_key.to_bytes().to_vec() };

    Ok(DiceData { evidence: Some(result_evidence), certificate_authority: Some(result_ca) })
}

/// Uses Stage0's measurements of the next stage to derive a Compound Device
/// Identifier (CDI) from a Unique Device Secret (UDS).
pub fn derive_sealing_cdi(
    uds: &DerivedKey,
    measurements: &oak_proto_rust::oak::attestation::v1::Stage0Measurements,
) -> DerivedKey {
    // Mix in the measurements of the kernel, the kernel command-line, the kernel
    // setup data and the initial RAM disk when deriving the CDI for Layer 1.
    let salt: Vec<u8> = {
        let mut salt = Vec::with_capacity(128);
        salt.extend_from_slice(&measurements.kernel_measurement);
        salt.extend_from_slice(shorten_cmdline(&measurements.kernel_cmdline).as_bytes());
        salt.extend_from_slice(&measurements.setup_data_digest);
        salt.extend_from_slice(&measurements.ram_disk_digest);
        salt
    };

    let mut result = DerivedKey::default();
    let hkdf = Hkdf::<Sha256>::new(Some(&salt), &uds[..]);
    hkdf.expand(b"CDI_Seal", &mut result[..]).expect("invalid length for HKDF output");
    result
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

fn encode_event_with_tag_and_type<T: prost::Message>(
    measurements: T,
    tag: &str,
    type_url: &str,
) -> Vec<u8> {
    let tag = String::from(tag);

    // When an any type is deserialized, the `type_url` is missing the
    // `type.googleapis.com{}` suffix. But we depend on it being there for this
    // attestation mechansim, so we manually create the Any struct rather than using
    // a generated version.
    let event = Some(prost_types::Any {
        type_url: type_url.to_string(),
        value: measurements.encode_to_vec(),
    });

    let event = oak_proto_rust::oak::attestation::v1::Event { tag, event };
    event.encode_to_vec()
}

pub fn encode_stage0_event(
    measurements: oak_proto_rust::oak::attestation::v1::Stage0Measurements,
) -> Vec<u8> {
    encode_event_with_tag_and_type(
        measurements,
        STAGE0_TAG,
        "type.googleapis.com/oak.attestation.v1.Stage0Measurements",
    )
}

pub fn encode_stage0_transparent_event(
    measurements: oak_proto_rust::oak::attestation::v1::Stage0TransparentMeasurements,
) -> Vec<u8> {
    encode_event_with_tag_and_type(
        measurements,
        STAGE0_TRANSPARENT_TAG,
        "type.googleapis.com/oak.attestation.v1.Stage0TransparentMeasurements",
    )
}

//
// Copyright 2024 The Project Oak Authors
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

//! Code to serialize attestation proto messages to JSON, in order to make them
//! human readable. This code is manually maintained for each struct, for two
//! reasons:
//! - to customize output to make it more readable, e.g. if the proto message is
//!   convoluted or to print binary digests as hex;
//! - a mix of lack of official proto support in rust and idiosyncracies of the
//!   bazel build system make it exceedingly difficult to auto-generated JSON
//!   mappings.
//!
//! Unfortunately this means that when these structs are updated, these bindings
//! will also need to be updated. Since the functions in this mod exhaustively
//! destructure each struct, the rust compiler ensures that they serialize all
//! properties, even as new ones are added.
//!
//! This implementation serializes these structs to [`serde_json::Value`], even
//! though in this crate they are eventually converted to yaml. The reason for
//! this is that [`serde_json`] implements a macro that makes this code a lot
//! more maintainable.

use oak_proto_rust::oak::{
    attestation::v1::{
        ApplicationLayerData, ApplicationLayerReferenceValues, ContainerLayerData,
        ContainerLayerReferenceValues, ExtractedEvidence, KernelLayerData,
        KernelLayerReferenceValues, OakContainersData, OakContainersReferenceValues,
        OakRestrictedKernelData, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerData, RootLayerReferenceValues, SystemLayerData, SystemLayerReferenceValues, *,
    },
    RawDigest,
};
use serde_json::json;

macro_rules! json {
    ($($json:tt)+) => {{
        let value = serde_json::json!($($json)+);
        match value {
            serde_json::Value::Object(mut map) => {
                // If a field on the struct is [`None`], it gets serialized as null in JSON.
                // For readability we can omit these null values, as null is the default value.
                map.retain(|_, v| !v.is_null());
                serde_json::Value::Object(map)
            },
            _ => value,
        }
    }};
}

pub fn serialize_root_layer_data(instance: &RootLayerData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let RootLayerData { report } = instance;
    match report {
        Some(root_layer_data::Report::SevSnp(instance)) => {
            json!({
                "sev_snp": serialize_amd_attestation_report(instance)
            })
        }
        Some(root_layer_data::Report::Tdx(instance)) => {
            json!({
                "tdx": serialize_intel_tdx_attestation_report(instance)
            })
        }
        Some(root_layer_data::Report::Fake(instance)) => {
            json!({
                "fake": serialize_fake_attestation_report(instance)
            })
        }
        None => json!(null),
    }
}

pub fn serialize_amd_attestation_report(instance: &AmdAttestationReport) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let AmdAttestationReport {
        report_data,
        current_tcb,
        reported_tcb,
        debug,
        initial_measurement,
        hardware_id,
        vmpl,
    } = instance;

    json!({
        "report_data": hex::encode(report_data),
        "current_tcb":  current_tcb.as_ref().map(serialize_tcb_version),
        "reported_tcb":  reported_tcb.as_ref().map(serialize_tcb_version),
        "debug": debug,
        "initial_measurement": hex::encode(initial_measurement),
        "hardware_id": hex::encode(hardware_id),
        "vmpl": vmpl,
    })
}

pub fn serialize_intel_tdx_attestation_report(
    instance: &IntelTdxAttestationReport,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let IntelTdxAttestationReport { report_data } = instance;

    json!({
        "report_data": hex::encode(report_data),
    })
}

pub fn serialize_fake_attestation_report(instance: &FakeAttestationReport) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let FakeAttestationReport { report_data } = instance;

    json!({
        "report_data": hex::encode(report_data),
    })
}

pub fn serialize_kernel_layer_data(instance: &KernelLayerData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let KernelLayerData {
        kernel_image,
        kernel_setup_data,
        kernel_raw_cmd_line,
        init_ram_fs,
        memory_map,
        acpi,
    } = instance;

    json!({
        "kernel_image": kernel_image.as_ref().map(serialize_raw_digest),
        "kernel_setup_data": kernel_setup_data.as_ref().map(serialize_raw_digest),
        "kernel_raw_cmd_line": kernel_raw_cmd_line,
        "init_ram_fs": init_ram_fs.as_ref().map(serialize_raw_digest),
        "memory_map": memory_map.as_ref().map(serialize_raw_digest),
        "acpi": acpi.as_ref().map(serialize_raw_digest),
    })
}

pub fn serialize_application_layer_data(instance: &ApplicationLayerData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ApplicationLayerData { binary, config } = instance;

    json!({
        "binary": binary.as_ref().map(serialize_raw_digest),
        "config": config.as_ref().map(serialize_raw_digest),
    })
}

pub fn serialize_system_layer_data(instance: &SystemLayerData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let SystemLayerData { system_image } = instance;

    json!({
        "system_image": system_image.as_ref().map(serialize_raw_digest),
    })
}

pub fn serialize_container_layer_data(instance: &ContainerLayerData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ContainerLayerData { bundle, config } = instance;

    json!({
        "bundle":  bundle.as_ref().map(serialize_raw_digest),
        "config": config.as_ref().map(serialize_raw_digest),
    })
}

pub fn serialize_event_data(instance: &EventData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let EventData { event } = instance;

    json!({
        "event": event.as_ref().map(serialize_raw_digest),
    })
}

pub fn serialize_oak_restricted_kernel_data(
    instance: &OakRestrictedKernelData,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let OakRestrictedKernelData { root_layer, kernel_layer, application_layer } = instance;

    json!({
        "root_layer":  root_layer.as_ref().map(serialize_root_layer_data),
        "kernel_layer":  kernel_layer.as_ref().map(serialize_kernel_layer_data),
        "application_layer": application_layer.as_ref().map(serialize_application_layer_data),
    })
}

pub fn serialize_oak_containers_data(instance: &OakContainersData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let OakContainersData { root_layer, kernel_layer, system_layer, container_layer } = instance;

    json!({
        "root_layer": root_layer.as_ref().map(serialize_root_layer_data),
        "kernel_layer": kernel_layer.as_ref().map(serialize_kernel_layer_data),
        "system_layer": system_layer.as_ref().map(serialize_system_layer_data),
        "container_layer": container_layer.as_ref().map(serialize_container_layer_data),
    })
}

pub fn serialize_cb_data(instance: &CbData) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let CbData { root_layer, kernel_layer, system_layer, application_layer } = instance;

    json!({
        "root_layer": root_layer.as_ref().map(serialize_root_layer_data),
        "kernel_layer":  kernel_layer.as_ref().map(serialize_event_data),
        "system_layer": system_layer.as_ref().map(serialize_event_data),
        "application_layer": application_layer.as_ref().map(serialize_event_data),
    })
}

pub fn serialize_oak_standalone_data(instance: &OakStandaloneData) -> serde_json::Value {
    let OakStandaloneData {} = instance;

    json!({})
}

pub fn serialize_extracted_evidence(instance: &ExtractedEvidence) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ExtractedEvidence { evidence_values, encryption_public_key, signing_public_key } = instance;

    match evidence_values {
        Some(extracted_evidence::EvidenceValues::OakRestrictedKernel(instance)) => {
            json!({
                "oak_restricted_kernel": serialize_oak_restricted_kernel_data(instance)
            })
        }
        Some(extracted_evidence::EvidenceValues::OakContainers(instance)) => {
            json!({
                "oak_containers": serialize_oak_containers_data(instance)
            })
        }
        Some(extracted_evidence::EvidenceValues::Cb(instance)) => {
            json!({
                "cb": serialize_cb_data(instance)
            })
        }
        Some(extracted_evidence::EvidenceValues::Standalone(instance)) => {
            json!({
                "encryption_public_key": hex::encode(encryption_public_key),
                "signing_public_key": hex::encode(signing_public_key),
                "standalone": serialize_oak_standalone_data(instance)
            })
        }
        None => json!(null),
    }
}

pub fn serialize_tcb_version(instance: &TcbVersion) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let TcbVersion { boot_loader, tee, snp, microcode } = instance;
    json!({
        "boot_loader": boot_loader,
        "tee": tee,
        "snp": snp,
        "microcode": microcode,
    })
}

pub fn serialize_raw_digest(instance: &RawDigest) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let RawDigest {
        psha2,
        sha1,
        sha2_256,
        sha2_512,
        sha3_512,
        sha3_384,
        sha3_256,
        sha3_224,
        sha2_384,
    } = instance;

    let mut map = serde_json::Map::new();

    if !psha2.is_empty() {
        map.insert("psha2".to_string(), json!(hex::encode(psha2)));
    }
    if !sha1.is_empty() {
        map.insert("sha1".to_string(), json!(hex::encode(sha1)));
    }
    if !sha2_256.is_empty() {
        map.insert("sha2_256".to_string(), json!(hex::encode(sha2_256)));
    }
    if !sha2_512.is_empty() {
        map.insert("sha2_512".to_string(), json!(hex::encode(sha2_512)));
    }
    if !sha3_512.is_empty() {
        map.insert("sha3_512".to_string(), json!(hex::encode(sha3_512)));
    }
    if !sha3_384.is_empty() {
        map.insert("sha3_384".to_string(), json!(hex::encode(sha3_384)));
    }
    if !sha3_256.is_empty() {
        map.insert("sha3_256".to_string(), json!(hex::encode(sha3_256)));
    }
    if !sha3_224.is_empty() {
        map.insert("sha3_224".to_string(), json!(hex::encode(sha3_224)));
    }
    if !sha2_384.is_empty() {
        map.insert("sha2_384".to_string(), json!(hex::encode(sha2_384)));
    }

    serde_json::Value::Object(map)
}

pub fn serialize_skip_verification(instance: &SkipVerification) -> serde_json::Value {
    let SkipVerification {} = instance;
    json!({})
}

fn serialize_verifying_key(instance: &VerifyingKey) -> serde_json::Value {
    let VerifyingKey { r#type, key_id, raw } = instance;
    json!({
        "type": r#type,
        "key_id": key_id,
        "raw": hex::encode(raw),
    })
}

fn serialize_verifying_key_set(instance: &VerifyingKeySet) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let VerifyingKeySet { keys } = instance;
    json!(keys.iter().map(serialize_verifying_key).collect::<Vec<serde_json::Value>>())
}

fn serialize_verifying_key_reference_value(
    instance: &VerifyingKeyReferenceValue,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let VerifyingKeyReferenceValue { r#type } = instance;
    match r#type {
        Some(verifying_key_reference_value::Type::Skip(instance)) => {
            json!({
                "skip": serialize_skip_verification(instance)
            })
        }
        Some(verifying_key_reference_value::Type::Verify(instance)) => {
            json!({
                "verify": serialize_verifying_key_set(instance)
            })
        }
        None => json!(null),
    }
}

fn serialize_claim_reference_value(instance: &ClaimReferenceValue) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    json!({
       "claim_types": instance.claim_types
    })
}

pub fn serialize_endorsement_reference_value(
    instance: &EndorsementReferenceValue,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    #[allow(deprecated)]
    let EndorsementReferenceValue {
        endorser_public_key,
        rekor_public_key,
        endorser,
        required_claims,
        rekor,
    } = instance;
    json!({
        "endorser_public_key": hex::encode(endorser_public_key),
        "rekor_public_key": hex::encode(rekor_public_key),
        "endorser": endorser.as_ref().map(serialize_verifying_key_set),
        "required_claims": required_claims.as_ref().map(serialize_claim_reference_value),
        "rekor": rekor.as_ref().map(serialize_verifying_key_reference_value),
    })
}

pub fn serialize_binary_reference_value(instance: &BinaryReferenceValue) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let BinaryReferenceValue { r#type } = instance;
    match r#type {
        Some(binary_reference_value::Type::Skip(instance)) => {
            json!({
                "skip": serialize_skip_verification(instance)
            })
        }
        Some(binary_reference_value::Type::Endorsement(instance)) => {
            json!({
                "endorsement": serialize_endorsement_reference_value(instance)
            })
        }
        Some(binary_reference_value::Type::Digests(instance)) => {
            json!({
                "digests": serialize_digests(instance)
            })
        }
        None => json!(null),
    }
}

pub fn serialize_kernel_digests(instance: &KernelDigests) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let KernelDigests { image, setup_data } = instance;
    json!({
        "image":  image.as_ref().map(serialize_digests),
        "setup_data": setup_data.as_ref().map(serialize_digests),
    })
}

pub fn serialize_kernel_binary_reference_value(
    instance: &KernelBinaryReferenceValue,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let KernelBinaryReferenceValue { r#type } = instance;
    match r#type {
        Some(kernel_binary_reference_value::Type::Skip(instance)) => {
            json!({
                "skip": serialize_skip_verification(instance)
            })
        }
        Some(kernel_binary_reference_value::Type::Endorsement(instance)) => {
            json!({
                "endorsement": serialize_endorsement_reference_value(instance)
            })
        }
        Some(kernel_binary_reference_value::Type::Digests(instance)) => {
            json!({
                "digests": serialize_kernel_digests(instance)
            })
        }
        None => json!(null),
    }
}

pub fn serialize_regex(instance: &Regex) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let Regex { value } = instance;
    json!(value)
}

pub fn serialize_string_literals(instance: &StringLiterals) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let StringLiterals { value } = instance;
    json!(value)
}

pub fn serialize_text_reference_value(instance: &TextReferenceValue) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let TextReferenceValue { r#type } = instance;
    match r#type {
        Some(text_reference_value::Type::Skip(instance)) => {
            json!({
                "skip": serialize_skip_verification(instance)
            })
        }
        Some(text_reference_value::Type::Endorsement(instance)) => {
            json!({
                "endorsement": serialize_endorsement_reference_value(instance)
            })
        }
        Some(text_reference_value::Type::Regex(instance)) => {
            json!({
                "regex": serialize_regex(instance)
            })
        }
        Some(text_reference_value::Type::StringLiterals(instance)) => {
            json!({
                "string_literals": serialize_string_literals(instance)
            })
        }
        None => json!(null),
    }
}

pub fn serialize_root_layer_reference_values(
    instance: &RootLayerReferenceValues,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let RootLayerReferenceValues { amd_sev, intel_tdx, insecure } = instance;
    json!({
        "amd_sev":  amd_sev.as_ref().map(serialize_amd_sev_reference_values),
        "intel_tdx":  intel_tdx.as_ref().map(serialize_intel_tdx_reference_values),
        "insecure":  insecure.as_ref().map(serialize_insecure_reference_values),
    })
}

pub fn serialize_amd_sev_reference_values(instance: &AmdSevReferenceValues) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let AmdSevReferenceValues { min_tcb_version, allow_debug, stage0 } = instance;
    json!({
        "min_tcb_version": min_tcb_version.as_ref().map(serialize_tcb_version),
        "allow_debug": allow_debug,
        "stage0": stage0.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_intel_tdx_reference_values(
    instance: &IntelTdxReferenceValues,
) -> serde_json::Value {
    let IntelTdxReferenceValues {} = instance;
    json!({})
}

pub fn serialize_insecure_reference_values(
    instance: &InsecureReferenceValues,
) -> serde_json::Value {
    let InsecureReferenceValues {} = instance;
    json!({})
}

pub fn serialize_digests(instance: &Digests) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let Digests { digests } = instance;
    json!(digests.iter().map(serialize_raw_digest).collect::<Vec<serde_json::Value>>())
}

pub fn serialize_kernel_layer_reference_values(
    instance: &KernelLayerReferenceValues,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let KernelLayerReferenceValues { kernel, kernel_cmd_line_text, init_ram_fs, memory_map, acpi } =
        instance;
    json!({
        "kernel": kernel.as_ref().map(serialize_kernel_binary_reference_value),
        "kernel_cmd_line_text": kernel_cmd_line_text.as_ref().map(serialize_text_reference_value),
        "init_ram_fs": init_ram_fs.as_ref().map(serialize_binary_reference_value),
        "memory_map": memory_map.as_ref().map(serialize_binary_reference_value),
        "acpi": acpi.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_system_layer_reference_values(
    instance: &SystemLayerReferenceValues,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let SystemLayerReferenceValues { system_image } = instance;
    json!({
        "system_image":  system_image.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_application_layer_reference_values(
    instance: &ApplicationLayerReferenceValues,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ApplicationLayerReferenceValues { binary, configuration } = instance;
    json!({
        "binary": binary.as_ref().map(serialize_binary_reference_value),
        "configuration": configuration.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_container_layer_reference_values(
    instance: &ContainerLayerReferenceValues,
) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ContainerLayerReferenceValues { binary, configuration } = instance;
    json!({
        "binary":  binary.as_ref().map(serialize_binary_reference_value),
        "configuration":  configuration.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_event_reference_values(instance: &EventReferenceValues) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let EventReferenceValues { event } = instance;
    json!({
        "event":  event.as_ref().map(serialize_binary_reference_value),
    })
}

pub fn serialize_oak_restricted_kernel_reference_values(
    instance: &OakRestrictedKernelReferenceValues,
) -> serde_json::Value {
    let OakRestrictedKernelReferenceValues { root_layer, kernel_layer, application_layer } =
        instance;
    json!({
        "root_layer":  root_layer.as_ref().map(serialize_root_layer_reference_values),
        "kernel_layer":  kernel_layer.as_ref().map(serialize_kernel_layer_reference_values),
        "application_layer":  application_layer.as_ref().map(serialize_application_layer_reference_values),
    })
}

pub fn serialize_oak_containers_reference_values(
    instance: &OakContainersReferenceValues,
) -> serde_json::Value {
    let OakContainersReferenceValues { root_layer, kernel_layer, system_layer, container_layer } =
        instance;
    json!({
        "root_layer": root_layer.as_ref().map(serialize_root_layer_reference_values),
        "kernel_layer": kernel_layer.as_ref().map(serialize_kernel_layer_reference_values),
        "system_layer":  system_layer.as_ref().map(serialize_system_layer_reference_values),
        "container_layer":  container_layer.as_ref().map(serialize_container_layer_reference_values),
    })
}

pub fn serialize_cb_reference_values(instance: &CbReferenceValues) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let CbReferenceValues { root_layer, kernel_layer, system_layer, application_layer } = instance;
    json!({
        "root_layer":  root_layer.as_ref().map(serialize_root_layer_reference_values),
        "kernel_layer": kernel_layer.as_ref().map(serialize_event_reference_values),
        "system_layer":  system_layer.as_ref().map(serialize_event_reference_values),
        "application_layer":  application_layer.as_ref().map(serialize_event_reference_values),
    })
}

pub fn serialize_reference_values(instance: &ReferenceValues) -> serde_json::Value {
    // Exhaustive destructuring (e.g., without ", ..") ensures this function handles
    // all fields. If a new field is added to the struct, this code won't
    // compile unless this destructuring operation is updated, thereby reminding us
    // to keep the serialization in sync manually.
    let ReferenceValues { r#type } = instance;
    match r#type {
        Some(reference_values::Type::OakRestrictedKernel(instance)) => {
            json!({
                "oak_restricted_kernel": serialize_oak_restricted_kernel_reference_values(instance)
            })
        }
        Some(reference_values::Type::OakContainers(instance)) => {
            json!({
                "oak_containers": serialize_oak_containers_reference_values(instance)
            })
        }
        Some(reference_values::Type::Cb(instance)) => {
            json!({
                "cb": serialize_cb_reference_values(instance)
            })
        }
        None => json!(null),
    }
}

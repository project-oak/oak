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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(not(feature = "bazel"))]
    let included_protos = vec![std::path::PathBuf::from("..")];
    #[cfg(feature = "bazel")]
    let included_protos = oak_proto_build_utils::get_common_proto_path("..");

    let proto_paths = [
        "../proto/attestation/attachment.proto",
        "../proto/attestation/dice.proto",
        "../proto/attestation/reference_value.proto",
        "../proto/attestation/endorsement.proto",
        "../proto/attestation/eventlog.proto",
        "../proto/attestation/evidence.proto",
        "../proto/attestation/expected_value.proto",
        "../proto/attestation/verification.proto",
        "../proto/containers/hostlib_key_provisioning.proto",
        "../proto/containers/interfaces.proto",
        "../proto/containers/orchestrator_crypto.proto",
        "../proto/crypto/certificate.proto",
        "../proto/crypto/crypto.proto",
        "../proto/digest.proto",
        "../proto/variant.proto",
        "../proto/oak_debug/service/oak_debug.proto",
        "../proto/oak_functions/abi.proto",
        "../proto/oak_functions/application_config.proto",
        "../proto/oak_functions/lookup_data.proto",
        "../proto/oak_functions/sdk/oak_functions_wasm.proto",
        "../proto/oak_functions/service/oak_functions.proto",
        "../proto/oak_functions/testing.proto",
        "../proto/packages/packages.proto",
        "../proto/restricted_kernel/initial_data.proto",
        "../proto/session/messages.proto",
        "../proto/session/service_streaming.proto",
        "../proto/session/session.proto",
        "../third_party/google/profile.proto",
    ];
    let mut config = prost_build::Config::new();

    config.btree_map(["."]);

    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_JSON");

    config.bytes(vec![
        ".oak.containers.GetImageResponse".to_string(),
        ".oak.functions.LookupDataEntry".to_string(),
        ".oak.functions.ExtendNextLookupDataRequest".to_string(),
    ]);

    let annotate_types = [
        "oak.session.v1.AttestRequest",
        "oak.session.v1.AttestResponse",
        "oak.session.v1.NoiseHandshakeMessage",
        "oak.session.v1.SessionBinding",
        "oak.session.v1.HandshakeRequest",
        "oak.session.v1.HandshakeResponse",
        "oak.session.v1.EncryptedMessage",
        "oak.session.v1.PlaintextMessage",
        "oak.session.v1.SessionRequest",
        "oak.session.v1.SessionRequestWithSessionId",
        "oak.session.v1.SessionResponse",
        "oak.session.v1.EndorsedEvidence",
        "oak.attestation.v1.Evidence",
        "oak.attestation.v1.Endorsements",
        "oak.attestation.v1.ApplicationKeys",
        "oak.attestation.v1.LayerEvidence",
        "oak.attestation.v1.RootLayerEvidence",
        "oak.attestation.v1.OakRestrictedKernelEndorsements",
        "oak.attestation.v1.RootLayerEndorsements",
        "oak.attestation.v1.KernelLayerEndorsements",
        "oak.attestation.v1.ApplicationLayerEndorsements",
        "oak.attestation.v1.TransparentReleaseEndorsement",
        "oak.attestation.v1.SystemLayerEndorsements",
        "oak.attestation.v1.ContainerLayerEndorsements",
        "oak.attestation.v1.CBEndorsements",
        "oak.attestation.v1.OakContainersEndorsements",
        "oak.attestation.v1.SignedEndorsement",
        "oak.attestation.v1.Signature",
        "oak.attestation.v1.Endorsement",
        "oak.attestation.v1.EventLog",
        "oak.Variant",
    ];

    let oneof_field_names = [
        "oak.session.v1.HandshakeRequest.handshake_type",
        "oak.session.v1.HandshakeResponse.handshake_type",
        "oak.session.v1.SessionRequest.request",
        "oak.session.v1.SessionResponse.response",
        "oak.attestation.v1.Endorsements.type",
    ];
    for message_type in annotate_types.iter().chain(oneof_field_names.iter()) {
        config.type_attribute(message_type, "#[derive(serde::Serialize, serde::Deserialize)]");
        config.type_attribute(message_type, "#[serde(rename_all = \"camelCase\")]");
    }

    for message_type in annotate_types.iter() {
        config.type_attribute(message_type, "#[serde(default)]");
    }

    for message_type in oneof_field_names {
        config.field_attribute(message_type, "#[serde(flatten)]");
    }

    let bytes_fields = [
        "oak.session.v1.EncryptedMessage.ciphertext",
        "oak.session.v1.NoiseHandshakeMessage.ephemeral_public_key",
        "oak.session.v1.NoiseHandshakeMessage.static_public_key",
        "oak.session.v1.NoiseHandshakeMessage.ciphertext",
        "oak.session.v1.SessionBinding.binding",
        "oak.attestation.v1.Signature.raw",
        "oak.attestation.v1.Endorsement.serialized",
        "oak.attestation.v1.Endorsement.subject",
        "oak.attestation.v1.SignedEndorsement.rekor_log_entry",
        "oak.attestation.v1.TransparentReleaseEndorsement.endorsement",
        "oak.attestation.v1.TransparentReleaseEndorsement.subject",
        "oak.attestation.v1.TransparentReleaseEndorsement.endorsement_signature",
        "oak.attestation.v1.TransparentReleaseEndorsement.rekor_log_entry",
        "oak.attestation.v1.RootLayerEndorsements.tee_certificate",
        "oak.Variant.id",
        "oak.Variant.value",
    ];
    for bytes_field in bytes_fields {
        config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data\")]");
    }

    let optional_bytes_fields = [
        "oak.session.v1.EncryptedMessage.associated_data",
        "oak.session.v1.EncryptedMessage.nonce",
    ];
    for bytes_field in optional_bytes_fields {
        config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data::option_bytes\")]");
    }

    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for proto_path in proto_paths.iter() {
        println!("cargo:rerun-if-changed={}", proto_path);
    }

    #[cfg(feature = "bazel")]
    oak_proto_build_utils::fix_prost_derives()?;

    Ok(())
}

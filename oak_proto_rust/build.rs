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
use std::collections::HashSet;

use annotation::AnnotationInfo;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let included_protos = oak_proto_build_utils::get_common_proto_path("..");

    let proto_paths = [
        "../proto/attestation/assertion.proto",
        "../proto/attestation/attachment.proto",
        "../proto/attestation/cb_eventlog.proto",
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
        "../proto/ctf_sha2/falsify.proto",
        "../proto/digest.proto",
        "../proto/oak_debug/service/oak_debug.proto",
        "../proto/oak_functions/abi.proto",
        "../proto/oak_functions/application_config.proto",
        "../proto/oak_functions/lookup_data.proto",
        "../proto/oak_functions/sdk/oak_functions_wasm.proto",
        "../proto/oak_functions/service/oak_functions.proto",
        "../proto/oak_functions/standalone/oak_functions_session.proto",
        "../proto/oak_functions/testing.proto",
        "../proto/oak_verity/oak_verity.proto",
        "../proto/packages/packages.proto",
        "../proto/restricted_kernel/initial_data.proto",
        "../proto/session/messages.proto",
        "../proto/session/service_streaming.proto",
        "../proto/session/session.proto",
        "../proto/variant.proto",
        "../third_party/google/profile.proto",
    ];

    let mut needed_types = HashSet::new();
    for t in [
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
        "oak.attestation.v1.Assertion",
        "oak.attestation.v1.Evidence",
        "oak.attestation.v1.Endorsements",
        "oak.attestation.v1.ApplicationKeys",
        "oak.attestation.v1.BinaryArgvRegexMeasurement",
        "oak.attestation.v1.CbLayer1TransparentEvent",
        "oak.attestation.v1.CbLayer2TransparentEvent",
        "oak.attestation.v1.LayerEvidence",
        "oak.attestation.v1.MpmPackage",
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
    ] {
        needed_types.insert(t.to_string());
    }
    let mut annotations = AnnotationInfo::collect_annotations(
        &proto_paths,
        &included_protos,
        "oak",
        |it: String| needed_types.contains(&it),
    )?;

    // setting optional to non-scalar fields make it not distringuishable.
    annotations
        .optional_bytes_fields
        .insert("oak.session.v1.EncryptedMessage.associated_data".to_string());
    annotations.optional_bytes_fields.insert("oak.session.v1.EncryptedMessage.nonce".to_string());

    assert!(needed_types.difference(&annotations.annotate_types).count() == 0);

    let mut config = prost_build::Config::new();

    config.btree_map(["."]);

    config.bytes(vec![
        ".oak.containers.GetImageResponse".to_string(),
        ".oak.functions.LookupDataEntry".to_string(),
        ".oak.functions.ExtendNextLookupDataRequest".to_string(),
    ]);

    annotations.apply(&mut config);

    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    Ok(())
}

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
        "../proto/crypto/crypto.proto",
        "../proto/digest.proto",
        "../proto/oak_functions/abi.proto",
        "../proto/oak_functions/application_config.proto",
        "../proto/oak_functions/lookup_data.proto",
        "../proto/oak_functions/sdk/oak_functions_wasm.proto",
        "../proto/oak_functions/service/oak_functions.proto",
        "../proto/oak_functions/testing.proto",
        "../proto/session/messages.proto",
        "../proto/session/service_streaming.proto",
        "../proto/session/session.proto",
    ];
    let mut config = prost_build::Config::new();

    config.btree_map(["."]);

    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_JSON");

    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    micro_rpc_build::compile(
        &[
            "../proto/oak_functions/testing.proto",
            "../proto/crypto/crypto.proto",
            "../proto/oak_functions/sdk/oak_functions_wasm.proto",
        ],
        &included_protos,
        Default::default(),
    );

    micro_rpc_build::compile(
        &["../proto/oak_functions/service/oak_functions.proto"],
        &included_protos,
        micro_rpc_build::CompileOptions {
            receiver_type: micro_rpc_build::ReceiverType::RefSelf,
            bytes: vec![
                ".oak.functions.LookupDataEntry".to_string(),
                ".oak.functions.ExtendNextLookupDataRequest".to_string(),
            ],
            extern_paths: vec![
                micro_rpc_build::ExternPath::new(".oak.crypto.v1", "crate::oak::crypto::v1"),
                micro_rpc_build::ExternPath::new(
                    ".oak.attestation.v1",
                    "crate::oak::attestation::v1",
                ),
            ],
            ..Default::default()
        },
    );

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for proto_path in proto_paths.iter() {
        println!("cargo:rerun-if-changed={}", proto_path);
    }

    #[cfg(feature = "bazel")]
    oak_proto_build_utils::fix_prost_derives()?;

    Ok(())
}

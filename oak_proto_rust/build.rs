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
    let proto_paths = [
        "../proto/crypto/crypto.proto",
        "../proto/attestation/attachment.proto",
        "../proto/attestation/dice.proto",
        "../proto/attestation/endorsement.proto",
        "../proto/attestation/expected_value.proto",
        "../proto/attestation/evidence.proto",
        "../proto/attestation/reference_value.proto",
        "../proto/attestation/verification.proto",
        "../proto/containers/interfaces.proto",
        "../proto/digest.proto",
        "../proto/oak_functions/abi.proto",
        "../proto/oak_functions/lookup_data.proto",
        "../proto/session/session.proto",
        "../proto/oak_functions/service/oak_functions.proto",
        "../proto/oak_functions/testing.proto",
    ];
    let mut config = prost_build::Config::new();

    config.btree_map(["."]);

    #[cfg(feature = "json")]
    let descriptor_path =
        std::path::PathBuf::from(std::env::var("OUT_DIR").expect("could not get OUT_DIR"))
            .join("proto_descriptor.bin");

    #[cfg(feature = "json")]
    config
        // Save descriptors to file
        .file_descriptor_set_path(&descriptor_path)
        // Map in pbjson-types
        .compile_well_known_types()
        .extern_path(".google.protobuf", "::pbjson_types");

    config
        .compile_protos(&proto_paths, &[
            "..",
            // We need to include the well-known protos ourselves
            "../external/com_google_protobuf/src/google/protobuf/_virtual_imports/empty_proto",
            "../external/com_google_protobuf/src/google/protobuf/_virtual_imports/descriptor_proto",
        ])
        .expect("proto compilation failed");

    #[cfg(feature = "json")]
    pbjson_build::Builder::new()
        .register_descriptors(
            &std::fs::read(descriptor_path).expect("failed to read descriptor_set"),
        )?
        .preserve_proto_field_names()
        .build(&["."])?;

    micro_rpc_build::compile(
        &["../proto/oak_functions/testing.proto", "../proto/crypto/crypto.proto"],
        &[
            "..",
            // We need to include the well-known protos ourselves
            "../external/com_google_protobuf/src/google/protobuf/_virtual_imports/descriptor_proto",
        ],
        Default::default(),
    );

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for proto_path in proto_paths.iter() {
        println!("cargo:rerun-if-changed={}", proto_path);
    }

    Ok(())
}

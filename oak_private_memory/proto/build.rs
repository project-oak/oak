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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(not(feature = "bazel"))]
    let included_protos = vec![std::path::PathBuf::from("../..")];
    #[cfg(feature = "bazel")]
    let included_protos = oak_proto_build_utils::get_common_proto_path("../..");

    let proto_paths = [
        "../../oak_private_memory/proto/sealed_memory.proto",
        "../../oak_private_memory/proto/database.proto",
    ];

    let mut config = prost_build::Config::new();

    let annotate_types = [
        "oak.private_memory.SealedMemoryRequest",
        "oak.private_memory.SealedMemoryResponse",
        "oak.private_memory.Memory",
        "oak.private_memory.AddMemoryRequest",
        "oak.private_memory.AddMemoryResponse",
        "oak.private_memory.GetMemoriesRequest",
        "oak.private_memory.GetMemoriesResponse",
        "oak.private_memory.ResetMemoryRequest",
        "oak.private_memory.ResetMemoryResponse",
        "oak.private_memory.InvalidRequestResponse",
        "oak.private_memory.KeySyncRequest",
        "oak.private_memory.KeySyncResponse",
        "oak.private_memory.GetMemoryByIdRequest",
        "oak.private_memory.GetMemoryByIdResponse",
    ];

    let oneof_field_names = [
        "oak.private_memory.SealedMemoryResponse.response",
        "oak.private_memory.SealedMemoryRequest.request",
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

    let bytes_fields = ["oak.private_memory.content"];
    for bytes_field in bytes_fields {
        config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data\")]");
    }

    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    #[cfg(feature = "bazel")]
    oak_proto_build_utils::fix_prost_derives()?;

    Ok(())
}

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
use std::{env, path::Path};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let oak_proto_path_env = "OAK_PROTO_PATH";
    let val = env::var(oak_proto_path_env).unwrap();
    let path = Path::new(&val);
    let path_str = path.parent().unwrap().parent().unwrap().parent().unwrap();

    #[cfg(not(feature = "bazel"))]
    let mut included_protos = vec![std::path::PathBuf::from("..")];
    #[cfg(feature = "bazel")]
    let mut included_protos = oak_proto_build_utils::get_common_proto_path("..");

    included_protos.push(path_str.to_path_buf());

    let proto_paths =
        ["../proto/sealed_memory.proto", "../proto/database.proto", "../proto/internal.proto"];

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
        "oak.private_memory.SearchMemoryRequest",
        "oak.private_memory.SearchMemoryResponse",
        "oak.private_memory.Embedding",
        "oak.private_memory.SearchResult",
    ];

    // `u64` fields in js are encoded as string when serializing to Json, which
    // matches the json proto spec. To solve this, we deserialize the field as a
    // string and then parse it as a u64. If the field is passed as a u64, we
    // simply return the number.
    let u64_fields = ["oak.private_memory.KeySyncRequest.uid"];

    for message_type in u64_fields {
        config.field_attribute(message_type, "#[serde(deserialize_with = \"serde_aux::field_attributes::deserialize_number_from_string\")]");
    }

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

    let bytes_fields = [
        "oak.private_memory.Memory.content",
        "oak.private_memory.KeySyncRequest.data_encryption_key",
    ];
    for bytes_field in bytes_fields {
        config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data\")]");
    }

    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    #[cfg(feature = "bazel")]
    oak_proto_build_utils::fix_prost_derives()?;

    Ok(())
}

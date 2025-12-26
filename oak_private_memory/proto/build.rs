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
        "oak.private_memory.KeyDerivationInfo",
        "oak.private_memory.UserRegistrationRequest",
        "oak.private_memory.UserRegistrationResponse",
        "oak.private_memory.SearchMemoryResultItem",
        "oak.private_memory.SearchMemoryQuery",
        "oak.private_memory.MemoryContent",
        "oak.private_memory.MemoryValue",
        "oak.private_memory.EmbeddingQuery",
        "oak.private_memory.ScoreRange",
        "oak.private_memory.ResultMask",
        "oak.private_memory.SealedMemoryWrapperRequest",
        "oak.private_memory.SealedMemoryWrapperResponse",
        "oak.private_memory.DeleteMemoryRequest",
        "oak.private_memory.DeleteMemoryResponse",
        "oak.private_memory.TextQuery",
        "oak.private_memory.QueryClauses",
        "oak.private_memory.LLMViews",
        "oak.private_memory.LLMView",
        "oak.private_memory.LLMViewContent",
        "oak.private_memory.LLMViewValue",
        "oak.private_memory.ParamValue",
    ];

    let oneof_field_names = [
        "oak.private_memory.SealedMemoryResponse.response",
        "oak.private_memory.SealedMemoryRequest.request",
        "oak.private_memory.SearchMemoryQuery.clause",
        "oak.private_memory.MemoryValue.value",
        "oak.private_memory.TextQuery.value",
        "oak.private_memory.LLMView.view",
        "oak.private_memory.LLMViewValue.value",
        "oak.private_memory.ParamValue.value",
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
        "oak.private_memory.KeySyncRequest.key_encryption_key",
        "oak.private_memory.UserRegistrationRequest.key_encryption_key",
        "oak.private_memory.KeyDerivationInfo.kek_salt",
        "oak.private_memory.MemoryValue.value.bytes_val",
    ];
    for bytes_field in bytes_fields {
        config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data\")]");
    }

    // 64 bit integer fields in js are encoded as string when serializing to Json,
    // which matches the json proto spec. To solve this, we deserialize the
    // field as a string and then parse it as a int. If the field is passed as a
    // int, we simply return the number.
    let int64_fields = ["oak.private_memory.MemoryValue.value.int64_val"];

    for message_type in int64_fields {
        config.field_attribute(message_type, "#[serde(deserialize_with = \"serde_aux::field_attributes::deserialize_number_from_string\")]");
    }

    // Enum converters
    config.field_attribute(
        "oak.private_memory.KeySyncResponse.status",
        "#[serde(with=\"crate::key_sync_response_status_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.UserRegistrationResponse.status",
        "#[serde(with=\"crate::user_registration_response_status_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.ResultMask.include_fields",
        "#[serde(with=\"crate::memory_field_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.EmbeddingQuery.metric_type",
        "#[serde(with=\"crate::embedding_query_metric_type_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.TextQuery.match_type",
        "#[serde(with=\"crate::text_query_match_type_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.QueryClauses.operator",
        "#[serde(with=\"crate::operator_converter\")]",
    );

    // Timestamp converters
    config.field_attribute(
        "oak.private_memory.Memory.created_timestamp",
        "#[serde(with=\"crate::timestamp_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.Memory.event_timestamp",
        "#[serde(with=\"crate::timestamp_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.Memory.expiration_timestamp",
        "#[serde(with=\"crate::timestamp_converter\")]",
    );
    config.field_attribute(
        "oak.private_memory.TextQuery.value.timestamp_val",
        "#[serde(with=\"crate::non_optional_timestamp_converter\")]",
    );

    config.enable_type_names();
    config.compile_protos(&proto_paths, &included_protos).expect("proto compilation failed");

    Ok(())
}

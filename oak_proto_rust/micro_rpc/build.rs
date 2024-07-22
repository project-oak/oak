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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(not(feature = "bazel"))]
    let included_protos = vec![std::path::PathBuf::from("../..")];
    #[cfg(feature = "bazel")]
    let included_protos = oak_proto_build_utils::get_common_proto_path("../..");

    micro_rpc_build::compile(
        &["../../proto/oak_functions/service/oak_functions.proto"],
        &included_protos,
        micro_rpc_build::CompileOptions {
            receiver_type: micro_rpc_build::ReceiverType::RefSelf,
            extern_paths: vec![micro_rpc_build::ExternPath::new(".oak", "oak_proto_rust::oak")],
            ..Default::default()
        },
    );

    micro_rpc_build::compile(
        &[
            "../../proto/oak_functions/testing.proto",
            "../../proto/oak_functions/sdk/oak_functions_wasm.proto",
        ],
        &included_protos,
        micro_rpc_build::CompileOptions {
            extern_paths: vec![micro_rpc_build::ExternPath::new(".oak", "oak_proto_rust::oak")],
            ..Default::default()
        },
    );

    Ok(())
}

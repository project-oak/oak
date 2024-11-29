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

use oak_grpc_utils::{generate_grpc_code, CodegenOptions, ExternPath};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let included_protos = oak_proto_build_utils::get_common_proto_path("../../../..");
    generate_grpc_code(
        &["../../../../oak_gcp/examples/echo/proto/echo.proto"],
        &included_protos,
        CodegenOptions {
            build_server: true,
            build_client: true,
            extern_paths: vec![ExternPath::new(".oak", "::oak_proto_rust::oak")],
        },
    )?;

    Ok(())
}

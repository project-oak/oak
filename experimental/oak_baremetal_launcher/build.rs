//
// Copyright 2022 The Project Oak Authors
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

use oak_utils::{generate_grpc_code, CodegenOptions};

const RUNTIME_INTERFACE_SCHEMA: &str = "../../experimental/oak_baremetal_runtime/schema.fbs";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    generate_grpc_code(
        "../../",
        &["grpc_unary_attestation/proto/unary_server.proto"],
        CodegenOptions {
            build_client: false,
            build_server: true,
            extern_paths: vec![],
        },
    )?;

    oak_idl_gen_structs::compile_structs(RUNTIME_INTERFACE_SCHEMA);
    oak_idl_gen_services::compile_services_servers(RUNTIME_INTERFACE_SCHEMA);
    oak_idl_gen_services::compile_services_async_clients(RUNTIME_INTERFACE_SCHEMA);

    Ok(())
}

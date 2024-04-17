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
//

use oak_grpc_utils::{generate_grpc_code, CodegenOptions, ExternPath};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Generate gRPC code for exchanging messages with clients.
    generate_grpc_code(
        &[
            "../proto/crypto/crypto.proto",
            "../proto/attestation/evidence.proto",
            "../proto/oak_functions/service/oak_functions.proto",
        ],
        &[".."],
        CodegenOptions {
            build_server: true,
            // The client is only used in the integration test.
            build_client: true,
            extern_paths: vec![ExternPath::new(
                ".oak.functions",
                "::oak_functions_service::proto::oak::functions",
            )],
        },
    )?;

    generate_grpc_code(
        &["../oak_containers/proto/interfaces.proto", "../proto/session/messages.proto"],
        &[".."],
        CodegenOptions { build_client: true, ..Default::default() },
    )?;

    Ok(())
}

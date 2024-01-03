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

use oak_grpc_utils::{generate_grpc_code, CodegenOptions};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Generate gRPC code for exchanging messages with clients.
    generate_grpc_code(
        "../",
        &[
            "oak_remote_attestation/proto/v1/messages.proto",
            "oak_remote_attestation/proto/v1/service_streaming.proto",
        ],
        CodegenOptions {
            build_server: true,
            ..Default::default()
        },
    )?;

    // Generate micro RPC code for exchanging messages with the enclave.
    micro_rpc_build::compile(
        &["proto/oak_functions/service/oak_functions.proto"],
        &[".."],
        Default::default(),
    );

    Ok(())
}

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

use oak_grpc_utils::{generate_grpc_code, CodegenOptions};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    generate_grpc_code(
        "../",
        &[
            "oak_remote_attestation_noninteractive/proto/v1/messages.proto",
            "oak_remote_attestation_noninteractive/proto/v1/service_streaming.proto",
        ],
        CodegenOptions {
            build_server: true,
            build_client: true,
            ..Default::default()
        },
    )?;

    Ok(())
}

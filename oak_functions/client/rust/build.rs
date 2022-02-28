//
// Copyright 2021 The Project Oak Authors
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

use oak_utils::{generate_grpc_code, CodegenOptions, ExternPath};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    generate_grpc_code(
        "../../../",
        &["oak_functions/proto/streaming_server.proto"],
        CodegenOptions {
            build_client: true,
            build_server: false,
            extern_paths: vec![ExternPath::new(
                ".oak.remote_attestation",
                "::oak_remote_attestation::proto",
            )],
        },
    )?;
    Ok(())
}

//
// Copyright 2020 The Project Oak Authors
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

use oak_utils::CodegenOptions;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let proto_path = "../../../";
    let file_path = "examples/hello_world/proto/hello_world.proto";

    oak_utils::generate_grpc_code(
        proto_path,
        &[file_path],
        CodegenOptions {
            build_client: true,
            ..Default::default()
        },
    )?;
    Ok(())
}

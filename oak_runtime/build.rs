//
// Copyright 2019 The Project Oak Authors
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

use oak_utils::{compile_protos_with_options, generate_grpc_code, CodegenOptions, ProtoOptions};

fn main() {
    generate_grpc_code(
        "../proto",
        &["authentication.proto"],
        CodegenOptions {
            build_server: true,
            ..Default::default()
        },
    )
    .expect("Proto compilation failed.");

    compile_protos_with_options(
        &[
            "../oak_services/proto/grpc_invocation.proto",
            "../oak_services/proto/http_invocation.proto",
            "../proto/introspection_events.proto",
        ],
        &[".."],
        ProtoOptions {
            ..Default::default()
        },
    );
}

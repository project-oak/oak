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

fn main() {
    // Exclude generation of service code, as it would require a reference to the Oak SDK to
    // compile.
    oak_utils::compile_protos_without_services(
        &[
            "../oak/proto/application.proto",
            "../oak/proto/grpc_encap.proto",
            "../oak/proto/label.proto",
            "../oak/proto/log.proto",
            "../oak/proto/oak_abi.proto",
            "../oak/proto/roughtime_service.proto",
            "../third_party/google/rpc/code.proto",
            "../third_party/google/rpc/status.proto",
        ],
        &[".."],
    );
}

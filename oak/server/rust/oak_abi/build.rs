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
    // TODO(#850): get Prost code generation working in Bazel.
    oak_utils::compile_protos_to(
        &[
            "../../../../oak/proto/grpc_encap.proto",
            "../../../../oak/proto/label.proto",
            "../../../../oak/proto/log.proto",
            "../../../../oak/proto/oak_abi.proto",
            "../../../../third_party/google/rpc/code.proto",
            "../../../../third_party/google/rpc/status.proto",
        ],
        &["../../../.."],
        "src/proto/",
    );
}

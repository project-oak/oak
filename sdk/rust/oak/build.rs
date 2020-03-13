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
    oak_utils::run_protoc_rust(protoc_rust::Args {
        out_dir: "src/proto",
        input: &[
            "../../../third_party/google/rpc/code.proto",
            "../../../third_party/google/rpc/status.proto",
            "../../../oak/proto/grpc_encap.proto",
            "../../../oak/proto/policy.proto",
            "../../../oak/proto/storage.proto",
            "../../../oak/proto/storage_channel.proto",
            "../../../oak/proto/log.proto",
        ],
        includes: &["../../.."],
        customize: protoc_rust::Customize::default(),
    })
    .expect("protoc");
}

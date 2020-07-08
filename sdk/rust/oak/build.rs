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
    oak_utils::compile_protos_with_options(
        &[
            "../../../oak/proto/storage_service.proto",
            "../../../oak/proto/roughtime_service.proto",
            "../../../oak/proto/handle.proto",
        ],
        &["../../.."],
        oak_utils::ProtoOptions {
            // We can't derive the HandleVisit trait as we are defining it in this crate.
            derive_handle_visit: false,
            ..Default::default()
        },
    );

    let mut handle_tests_out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    handle_tests_out.push("handle_tests");
    std::fs::create_dir_all(&handle_tests_out).unwrap();
    oak_utils::compile_protos_with_options(
        &["tests/handle_extract_inject.proto"],
        &["tests/", "../../../oak/proto"],
        oak_utils::ProtoOptions {
            out_dir_override: Some(handle_tests_out),
            ..Default::default()
        },
    );
}

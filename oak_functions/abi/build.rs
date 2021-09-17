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

extern crate prost_build;

fn main() {
    let file_paths = [
        "oak_functions/proto/abi.proto",
        "oak_functions/proto/lookup_data.proto",
        "oak_functions/proto/invocation.proto",
    ];
    prost_build::compile_protos(&file_paths, &["../.."]).expect("Proto compilation failed");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for proto_path in file_paths.iter() {
        let file_path = std::path::Path::new(proto_path);
        println!("cargo:rerun-if-changed=../../{}", file_path.display());
    }
}

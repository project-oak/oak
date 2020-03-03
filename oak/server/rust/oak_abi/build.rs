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

use std::path;

fn main() {
    let proto_dir = path::Path::new("../../../../oak/proto/");
    let oak_api_path = proto_dir.join("oak_api.proto");

    // Tell Cargo that if the given file changes, to rerun this build script.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#rerun-if-changed
    println!("cargo:rerun-if-changed={:?}", oak_api_path);

    prost_build::Config::new()
        .out_dir("src/proto")
        .compile_protos(&[&*oak_api_path],
                        &[proto_dir]).unwrap();

    std::fs::write("src/proto/mod.rs", "pub mod oak;").unwrap();
}

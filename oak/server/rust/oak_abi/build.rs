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
    let proto_files = vec!["oak_api.proto", "label.proto"];

    let proto_dir = path::Path::new("../../../../oak/proto/").to_path_buf();
    let proto_paths: Vec<path::PathBuf> = proto_files.iter().map(|f| proto_dir.join(f)).collect();

    // Tell Cargo that if any of the given files change, to rerun this build script.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#rerun-if-changed
    for path in &proto_paths {
        println!("cargo:rerun-if-changed={}", path.to_str().unwrap());
    }

    prost_build::Config::new()
        .type_attribute(".oak.label", "#[derive(Eq,Hash)]")
        .compile_protos(&proto_paths, &[proto_dir])
        .unwrap();
}

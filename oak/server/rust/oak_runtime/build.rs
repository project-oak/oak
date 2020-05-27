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

use std::path::Path;

fn main() {
    let proto_path = Path::new("../../../../oak/proto");
    let file_path = proto_path.join("authentication.proto");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    println!("cargo:rerun-if-changed={}", file_path.display());

    // Build `authentication.proto` with `tonic-build` rather than `oak_utils` as it runs directly
    // as a tonic service inside the gRPC server node rather than in a separate Wasm Node.
    tonic_build::configure()
        .build_client(false)
        .build_server(true)
        .compile(&[file_path.as_path()], &[proto_path])
        .expect("Proto compilation failed.");
}

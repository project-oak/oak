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

use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // TODO(#1093): drop this client crate and move all proto generation to common crate.
    let proto_path = Path::new("../proto");
    let file_path = proto_path.join("hello_world.proto");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    println!("cargo:rerun-if-changed={}", file_path.display());

    // Generate the normal (non-Oak) server and client code for the gRPC service,
    // along with the Rust types corresponding to the message definitions.
    tonic_build::configure()
        .build_client(true)
        .build_server(false)
        .compile(&[file_path.as_path()], &[proto_path])?;
    Ok(())
}

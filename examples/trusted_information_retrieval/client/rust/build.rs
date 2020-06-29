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
    // TODO(#1120): Add Rust client library function for building Protobuf.
    let proto_path = Path::new("../../proto");
    let trusted_information_retrieval_path = proto_path.join("trusted_information_retrieval.proto");
    let database_path = proto_path.join("database.proto");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    println!(
        "cargo:rerun-if-changed={}",
        trusted_information_retrieval_path.display()
    );
    println!("cargo:rerun-if-changed={}", database_path.display());

    tonic_build::configure()
        .build_client(true)
        .build_server(false)
        .compile(
            &[
                trusted_information_retrieval_path.as_path(),
                database_path.as_path(),
            ],
            &[proto_path],
        )?;
    Ok(())
}

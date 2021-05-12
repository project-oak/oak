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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let proto_path = std::path::Path::new("../proto");
    let file_paths = &["server.proto"];
    let file_paths: Vec<std::path::PathBuf> = file_paths
        .iter()
        .map(|file_path| proto_path.join(file_path))
        .collect();

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for file_path in file_paths.iter() {
        println!("cargo:rerun-if-changed={}", file_path.display());
    }

    set_protoc_env_if_unset();

    // Generate gRPC server along with the Rust types corresponding to the message definitions.
    tonic_build::configure()
        .build_client(false)
        .build_server(true)
        .extern_path(".oak.functions.invocation", "::oak_functions_abi::proto")
        .compile(&file_paths, &[proto_path.to_path_buf()])?;

    Ok(())
}

fn set_protoc_env_if_unset() {
    if std::env::var("PROTOC").is_err() {
        // Use the system protoc if no override is set, so prost-build does not try to use the
        // bundled one that we remove as part of the vendoring process.
        std::env::set_var("PROTOC", "protoc");
    }
}

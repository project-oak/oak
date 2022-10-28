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

/// Options for building gRPC code.
#[derive(Default)]
pub struct CodegenOptions {
    /// Specify whether to build client related code.
    pub build_client: bool,
    /// Specify whether to build server related code.
    pub build_server: bool,
    /// Specify externally provided Protobuf packages or types.
    pub extern_paths: Vec<ExternPath>,
}

#[derive(Default)]
pub struct ExternPath {
    proto_path: String,
    rust_path: String,
}

impl ExternPath {
    pub fn new(proto_path: &str, rust_path: &str) -> Self {
        ExternPath {
            proto_path: proto_path.to_string(),
            rust_path: rust_path.to_string(),
        }
    }
}

/// Generate gRPC code from Protobuf using `tonic` library.
///
/// The path to the root repository must be passed as `proto_path`. All paths to `.proto` files
/// must be specified relative to this path. Likewise, all imported paths in `.proto` files must
/// be specified relative to this path.
pub fn generate_grpc_code(
    proto_path: &str,
    file_paths: &[&str],
    options: CodegenOptions,
) -> std::io::Result<()> {
    set_protoc_env_if_unset();

    // TODO(#1093): Move all proto generation to a common crate.
    let proto_path = std::path::Path::new(proto_path);
    let file_paths: Vec<std::path::PathBuf> = file_paths
        .iter()
        .map(|file_path| proto_path.join(file_path))
        .collect();

    // Generate the normal (non-Oak) server and client code for the gRPC service,
    // along with the Rust types corresponding to the message definitions.
    let mut config = tonic_build::configure()
        .build_client(options.build_client)
        .build_server(options.build_server);

    for extern_path in options.extern_paths {
        config = config.extern_path(extern_path.proto_path, extern_path.rust_path);
    }
    config.compile(&file_paths, &[proto_path.to_path_buf()])
}

fn set_protoc_env_if_unset() {
    if std::env::var("PROTOC").is_err() {
        // Use the system protoc if no override is set, so prost-build does not try to use the
        // bundled one that we remove as part of the vendoring process.
        std::env::set_var("PROTOC", "protoc");
    }
}

/// Trait for logging error messages
pub trait LogError {
    fn log_error(&self, error: &str);
}

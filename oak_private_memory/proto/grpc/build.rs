//
// Copyright 2025 The Project Oak Authors
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

use std::env;

use oak_grpc_utils::{generate_grpc_code, CodegenOptions, ExternPath};

macro_rules! pathbufs {
    ( $( $x:expr ),* $(,)? ) => {
        &[ $( std::path::PathBuf::from($x) ),* ]
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let r = runfiles::Runfiles::create().expect("Couldn't initialize runfiles");
    let oak_runfiles_path =
        runfiles::rlocation!(r, "oak").expect("Couldn't get runfile path for oak");
    let googleapis_runfile_path =
        runfiles::rlocation!(r, "googleapis").expect("Couldn't get runfile path for googleapis");

    let mut included_protos = oak_proto_build_utils::get_common_proto_path("../..");

    included_protos.push(oak_runfiles_path);
    included_protos.push(googleapis_runfile_path);

    let proto_paths = pathbufs!("../../proto/sealed_memory.proto", "../../proto/database.proto");
    generate_grpc_code(
        proto_paths,
        &included_protos,
        CodegenOptions {
            build_server: true,
            build_client: true,
            extern_paths: vec![
                ExternPath::new(".oak", "::oak_proto_rust::oak"),
                ExternPath::new(
                    ".oak.private_memory",
                    "::sealed_memory_rust_proto::oak::private_memory",
                ),
            ],
        },
    )?;
    Ok(())
}

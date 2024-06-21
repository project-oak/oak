//
// Copyright 2023 The Project Oak Authors
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

use std::path::PathBuf;

use oak_grpc_utils::{generate_grpc_code, CodegenOptions};

#[cfg(feature = "bazel")]
fn get_included_protos() -> Vec<PathBuf> {
    // The root of all Oak protos
    let oak_proto_root = PathBuf::from("..");
    // Rely on bazel make variable `location` to find protobuf include paths.
    // We do this as protobuf might be imported under different names in the
    // external directory based on the setup (BzlMod, WORKSPACE or others).
    // Possible names are: com_google_protobuf, protobuf~, and protobuf.
    // The goal is to allow dependent repositories to use this
    // library without renaming their explicit import of protobuf library.
    // We use descriptor_proto_srcs instead of well_known_type_protos as the latter
    // returns a number of files and `locations` make variable returns a list of
    // relative location and not absolute paths.
    let protobuf_include_path = PathBuf::from(
        std::env::var("DESCRIPTOR_PROTO_PATH")
            .unwrap()
            .replace("google/protobuf/descriptor.proto", ""),
    );
    vec![oak_proto_root, protobuf_include_path]
}

#[cfg(not(feature = "bazel"))]
fn get_included_protos() -> Vec<PathBuf> {
    // The root of all Oak protos, relative to this directory.
    let oak_proto_root = PathBuf::from("..");

    // In cargo mode, the protoc invocations already include the google
    // protobufs, so we only need to provide the Oak proto root.
    vec![oak_proto_root]
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let included_protos = get_included_protos();
    // Generate gRPC code for connecting to the launcher.
    generate_grpc_code(
        &[
            "../proto/containers/interfaces.proto",
            "../proto/crypto/crypto.proto",
            "../proto/key_provisioning/key_provisioning.proto",
            "../proto/containers/hostlib_key_provisioning.proto",
            "../proto/session/messages.proto",
        ],
        &included_protos,
        CodegenOptions { build_client: true, build_server: true, ..Default::default() },
    )?;

    Ok(())
}

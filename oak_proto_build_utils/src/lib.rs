// Copyright 2024 The Project Oak Authors
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

/// Returns the include paths of common protos
///
///  Oak proto and com_google_protobuf.
pub fn get_common_proto_path(root: &str) -> Vec<PathBuf> {
    // The root of all Oak protos
    let oak_proto_root = PathBuf::from(root);
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

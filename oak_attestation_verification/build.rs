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
//

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let proto_paths = [
        "proto/attestation/endorsement.proto",
        "proto/attestation/evidence.proto",
        "proto/attestation/reference_value.proto",
        "proto/attestation/verification.proto",
    ];
    prost_build::compile_protos(&proto_paths, &[".."]).expect("proto compilation failed");

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for proto_path in proto_paths.iter() {
        let file_path = std::path::Path::new(proto_path);
        println!(
            "cargo:rerun-if-changed={}{}",
            env!("WORKSPACE_ROOT"),
            file_path.display()
        );
    }

    Ok(())
}

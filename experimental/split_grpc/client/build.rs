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

const PROTO_PATH: &'static str = "../../../examples/hello_world/proto/";
const SOURCE_FILE: &'static str = "hello_world.proto";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let file_path = std::format!("{}{}", PROTO_PATH, SOURCE_FILE);
    tonic_build::configure()
        .build_client(true)
        .build_server(false)
        .out_dir("src/proto")
        .compile(&[Path::new(&file_path)], &[Path::new(PROTO_PATH)])?;

    // Tell cargo to not rerun this script unless the proto file has changed.
    // This is required because the proto compiler is outputting the file into the source tree.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    println!("cargo:rerun-if-changed={}", file_path);
    Ok(())
}

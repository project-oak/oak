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

use std::{
    fs::{copy, File},
    io::Write,
    path::PathBuf,
};

// returns source_path if it can be constructed and if it points to a valid file
fn try_source_path() -> Result<PathBuf, &'static str> {
    let kernel_directory = "oak_restricted_kernel_bin";
    let file_name = std::env::var("OAK_RESTRICTED_KERNEL_FILE_NAME").map_err(|_| {
            "the correct env variable OAK_RESTRICTED_KERNEL_FILE_NAME must be set with the file name of the kernel build."
    })?;

    // The source file is the output from building "../oak_restricted_kernel_bin" in release mode.
    let mut source_path = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    source_path.pop();
    source_path.push(kernel_directory);
    source_path.push("target/x86_64-unknown-none/release");
    source_path.push(file_name);
    println!("cargo:rerun-if-changed={:?}", &source_path);
    match source_path.exists() {
        true => Ok(source_path),
        false => Err("contructed source_path does not exist"),
    }
}

fn main() {
    println!("cargo:rerun-if-changed=cargo:rerun-if-env-changed=OAK_RESTRICTED_KERNEL_FILE_NAME");
    println!("cargo:rerun-if-changed=layout.ld");
    println!("cargo:rustc-link-arg=--script=layout.ld");
    let mut destination_path = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    match try_source_path() {
        Ok(source_path) => {
            destination_path.push(source_path.file_name().unwrap());
            copy(&source_path, &destination_path).unwrap();
        }
        Err(msg) => {
            let msg = format!(
                "Kernel could not be built! An error occured when building: {}",
                msg
            );
            println!("cargo:warning={}", msg.as_str());
            // Create a fake file so cargo clippy doesn't break if the kernel was not built.
            destination_path.push("invalid_build");
            File::create(&destination_path)
                .unwrap()
                .write_all(msg.as_bytes())
                .unwrap();
        }
    }

    println!(
        "cargo:rustc-env=PAYLOAD_PATH={}",
        destination_path.to_str().unwrap()
    );
}

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

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::Path;

#[cfg(test)]
mod tests;

// This function uses `protoc_rust` to generate Rust `proto` files in a temporary directory,
// checks previously generated files and updates them if their contents have changed.
// This is a workaround for `protoc_rust` that always updates files, thus provoking recompilation
// of all dependent targets.
// Function doesn't support nested directories since `protoc_rust` doesn't generate them.
pub fn run_protoc_rust(args: protoc_rust::Args) -> io::Result<()> {
    let out_path = Path::new(args.out_dir);

    // Create a temporary directory.
    let temp_dir = tempfile::tempdir()?;
    let temp_path = temp_dir.path();

    // Generate Rust `proto` files in the temporary directory.
    let mut temp_args = args;
    temp_args.out_dir = temp_path.to_str().expect("Temporary path error");
    protoc_rust::run(temp_args)?;

    // Copy updated Rust `proto` files to the `out_path`.
    copy_updated_files(temp_path, out_path)?;

    Ok(())
}

// This function is identical to `run_protoc_rust` but uses `protoc_rust_grpc` instead.
pub fn run_protoc_rust_grpc(args: protoc_rust_grpc::Args) -> io::Result<()> {
    let out_path = Path::new(args.out_dir);

    // Create a temporary directory.
    let temp_dir = tempfile::tempdir()?;
    let temp_path = temp_dir.path();

    // Generate Rust `grpc` files in the temporary directory.
    let mut temp_args = args;
    temp_args.out_dir = temp_path.to_str().expect("Temporary path error");
    protoc_rust_grpc::run(temp_args)?;

    // Copy updated Rust `grpc` files to the `out_path`.
    copy_updated_files(temp_path, out_path)?;

    Ok(())
}

// This function traverses `dir` and gets a `HashMap` of filenames and their contents.
fn get_files(dir: &Path) -> HashMap<String, String> {
    walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(|entry| entry.ok())
        .filter(|entry| entry.path().is_file())
        .map(|entry| {
            let path = entry.into_path();
            let content = fs::read_to_string(&path).expect("Read error");
            let filename = path
                .file_name()
                .expect("Filename error")
                .to_os_string()
                .into_string()
                .expect("OsString error");
            (filename, content)
        })
        .collect()
}

// This function returns a list of files in the `new_dir` that are different from files with
// same names in the `old_dir`.
fn get_updated_files(old_dir: &Path, new_dir: &Path) -> Vec<String> {
    let old_files = get_files(old_dir);
    get_files(new_dir)
        .iter()
        .filter_map(|(filename, content)| {
            old_files
                .get(filename)
                .map_or(Some(filename), |old_content| {
                    if content == old_content {
                        None
                    } else {
                        Some(filename)
                    }
                })
        })
        .cloned()
        .collect()
}

// This function copies updated files from `src_dir` to `dst_dir` directory.
fn copy_updated_files(src_dir: &Path, dst_dir: &Path) -> io::Result<()> {
    let updated_files = get_updated_files(dst_dir, src_dir);
    for updated_file in updated_files.iter() {
        fs::copy(src_dir.join(&updated_file), dst_dir.join(&updated_file))?;
    }
    Ok(())
}

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

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io;
use std::io::Write;
use std::path::Path;

#[cfg(test)]
mod tests;

// Generates Rust `proto` files in a temporary directory using `protoc_rust`,
// checks previously generated files and updates them if their contents have changed.
// This is a workaround for `protoc_rust` issue that always updates files, thus provoking
// recompilation of all dependent targets.
// https://github.com/rust-lang/cargo/issues/6529
// Function doesn't support nested directories since `protoc_rust` doesn't generate them.
pub fn run_protoc_rust(args: protoc_rust::Args) -> io::Result<()> {
    let out_dir_path = Path::new(args.out_dir);

    // Create a temporary directory.
    let temp_dir = tempfile::tempdir()?;
    let temp_dir_path = temp_dir.path();

    // Generate Rust `proto` files in the temporary directory.
    let mut temp_args = args;
    temp_args.out_dir = temp_dir_path.to_str().expect("Temporary path error");
    protoc_rust::run(temp_args)?;

    // Copy changed Rust `proto` files to the `out_dir_path`.
    update_files(temp_dir_path, out_dir_path)?;

    Ok(())
}

// Generates Rust `proto` files in a temporary directory using `run_protoc_rust`,
// checks previously generated files and updates them if their contents have changed.
pub fn run_protoc_rust_grpc(args: protoc_rust_grpc::Args) -> io::Result<()> {
    let out_dir_path = Path::new(args.out_dir);

    // Create a temporary directory.
    let temp_dir = tempfile::tempdir()?;
    let temp_dir_path = temp_dir.path();

    // Generate Rust `grpc` files in the temporary directory.
    let mut temp_args = args;
    temp_args.out_dir = temp_dir_path.to_str().expect("Temporary path error");
    protoc_rust_grpc::run(temp_args)?;

    // Copy changed Rust `grpc` files to the `out_dir_path`.
    update_files(temp_dir_path, out_dir_path)?;

    Ok(())
}

#[derive(Debug, Eq, PartialEq, Hash)]
struct FileDiff {
    filename: String,
    old_content: Option<String>,
    new_content: Option<String>,
}

#[derive(Debug, Eq, PartialEq)]
enum FileAction {
    Ignore,
    Remove,
    Update { new_content: String },
}

impl FileDiff {
    // Returns a file action based on whether file contents were changed or not.
    fn action(&self) -> FileAction {
        match (self.old_content.as_ref(), self.new_content.as_ref()) {
            (Some(old_content), Some(new_content)) => {
                if old_content == new_content {
                    FileAction::Ignore
                } else {
                    FileAction::Update {
                        new_content: new_content.to_string(),
                    }
                }
            }
            (Some(_), None) => {
                // `mod.rs` file is not generated by `protoc_rust` and `protoc_rust_grpc`.
                if "mod.rs" == self.filename {
                    FileAction::Ignore
                } else {
                    FileAction::Remove
                }
            }
            (None, Some(new_content)) => FileAction::Update {
                new_content: new_content.to_string(),
            },
            _ => FileAction::Ignore,
        }
    }
}

// Copies changed files from `temp_path` to `path` and removes files from `path`
// that are not present in `temp_path`.
fn update_files(temp_path: &Path, path: &Path) -> io::Result<()> {
    let files = get_files(path);
    let temp_files = get_files(temp_path);
    get_file_diffs(&files, &temp_files)
        .iter()
        .try_for_each(|diff| {
            let filepath = path.join(&diff.filename);
            match diff.action() {
                FileAction::Ignore => Ok(()),
                FileAction::Remove => fs::remove_file(filepath),
                FileAction::Update { new_content } => {
                    // `File::create` truncates an existing file.
                    let mut file = fs::File::create(filepath).unwrap();
                    file.write_all(new_content.as_bytes())
                }
            }
        })
}

// Returns a hash set of file differences that represent old and new contents.
fn get_file_diffs(
    old_files: &HashMap<String, String>,
    new_files: &HashMap<String, String>,
) -> HashSet<FileDiff> {
    let file_set = old_files
        .keys()
        .chain(new_files.keys())
        .cloned()
        .collect::<HashSet<String>>();
    file_set
        .iter()
        .map(|filename| FileDiff {
            filename: filename.to_string(),
            old_content: old_files.get(filename).cloned(),
            new_content: new_files.get(filename).cloned(),
        })
        .collect()
}

// Traverses `dir` and produces a `HashMap` of filenames and their contents.
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

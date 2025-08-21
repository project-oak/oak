//
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
//

pub mod bad_todos;
pub mod build_license;
pub mod buildifier;
pub mod clang_format;
pub mod hadolint;
pub mod ktfmt;
pub mod markdownlint;
pub mod prettier;
pub mod rustfmt;
pub mod shell_check;
pub mod source_license;
pub mod terraform;

use std::{
    fs::File,
    io::{BufReader, Read},
    path::Path,
    process::Command,
};

fn has_extension(path: &Path, extensions: &[&str]) -> bool {
    match path.extension() {
        Some(ex) => extensions.contains(&ex.to_string_lossy().as_ref()),
        _ => false,
    }
}

fn has_filename(path: &Path, names: &[&str]) -> bool {
    match path.file_name() {
        Some(name) => names.contains(&name.to_string_lossy().as_ref()),
        _ => false,
    }
}

fn contents_starts_with(path: &Path, bytes: &[u8]) -> anyhow::Result<bool> {
    let f = BufReader::new(File::open(path)?);
    let start: std::io::Result<Vec<u8>> = f.bytes().take(bytes.len()).collect();
    Ok(start? == bytes)
}

fn linter_command(command: &str, args: &[&str], path: &Path) -> anyhow::Result<linter::Outcome> {
    Command::new(command).args(args).arg(path.to_str().unwrap()).try_into()
}

trait QuietSuccess {
    fn quiet_success(self) -> linter::Outcome;
}

impl QuietSuccess for linter::Outcome {
    fn quiet_success(self) -> linter::Outcome {
        match self {
            linter::Outcome::Success(_) => linter::Outcome::Success("".to_string()),
            x => x,
        }
    }
}

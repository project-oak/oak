//
// Copyright 2026 The Project Oak Authors
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

//! Command line argument shapes shared by both binaries.

use std::{
    convert::Infallible,
    path::{Path, PathBuf},
};

use oak_digest::{DigestSet, hex_digest_from_typed_hash, hex_to_set_digest};

/// Reads relative paths from the invoking directory rather than the runfiles
/// tree. See <https://bazel.build/docs/user-manual#running-executables>.
fn resolve(path: &str) -> PathBuf {
    Path::new(&std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default()).join(path)
}

/// Parses a plain path argument. See [`resolve`].
pub fn parse_path(arg: &str) -> Result<PathBuf, Infallible> {
    Ok(resolve(arg))
}

/// Parses a `name=path` subject, defaulting the name to the file name.
pub fn parse_named_path(arg: &str) -> Result<(String, PathBuf), String> {
    let (name, path) = match arg.split_once('=') {
        Some((name, path)) => (name.to_string(), resolve(path)),
        None => {
            let path = resolve(arg);
            let name = path
                .file_name()
                .ok_or_else(|| format!("{arg} has no file name, pass name=path"))?
                .to_string_lossy()
                .into_owned();
            (name, path)
        }
    };
    if name.is_empty() {
        return Err(format!("{arg} has an empty subject name"));
    }
    Ok((name, path))
}

/// Parses a `name=algorithm:hex` subject that is not a local file.
pub fn parse_named_digest(arg: &str) -> Result<(String, DigestSet), String> {
    let (name, typed_hash) =
        arg.split_once('=').ok_or_else(|| format!("{arg} is not name=algorithm:hex"))?;
    let (_, hex) =
        typed_hash.split_once(':').ok_or_else(|| format!("{typed_hash} is not algorithm:hex"))?;
    if name.is_empty() {
        return Err(format!("{arg} has an empty subject name"));
    }
    if hex.is_empty() || !hex.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()) {
        return Err(format!("{hex} is not lowercase hex"));
    }
    // `oak_digest` rejects unknown algorithms and returns in-toto's spelling,
    // so `sha2_256` and `sha256` both end up as `sha256`.
    let digest = hex_digest_from_typed_hash(typed_hash).map_err(|e| format!("{e:#}"))?;
    Ok((name.to_string(), hex_to_set_digest(&digest)))
}

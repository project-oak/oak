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

use std::path::{Path, PathBuf};

pub fn data_path(path: impl AsRef<Path>) -> PathBuf {
    const DATA_PATH_PREFIX: &str = "oak";
    let mut pb: PathBuf = DATA_PATH_PREFIX.into();
    pb.push(path);

    let r = runfiles::Runfiles::create().expect("Couldn't initialize runfiles");
    let p = runfiles::rlocation!(r, &pb).expect("Couldn't get runfile path");
    if !p.exists() {
        panic!("Data dependency not found: {}", pb.display());
    }
    p
}

/// Reads a test data file as raw bytes.
///
/// The macro assumes that the crate follows this structure, and expects the
/// file path to be relative to the `testdata` directory.
///
/// ```text
/// crate_name/
///  ├── src/
///  │   └── lib.rs
///  ├── testdata/
///  │   └── test.txt
///  └── BUILD
/// ```
///
/// ## Example
///
/// ```rust,ignore
/// use oak_file_utils::read_testdata;
///
/// let contents = read_testdata!("test.txt");
/// ```
#[macro_export]
macro_rules! read_testdata {
    ($file:expr) => {{
        let this_file = std::file!();
        // file! gives a path relative to the workspace root, e.g.,
        // "oak_attestation_gcp/src/policy.rs". We want to find the crate directory
        // by finding the "src" directory and taking its parent.
        let src_pos = this_file
            .rfind("/src/")
            .expect(&format!("could not find `/src/` in path from file! macro: {this_file}"));
        let crate_dir = &this_file[..src_pos];
        let testdata_path = format!("{}/testdata/{}", crate_dir, $file);
        let file_path = $crate::data_path(&testdata_path);
        std::fs::read(&file_path).expect(&format!("failed to read testdata file '{}'", $file))
    }};
}

/// Reads a test data file as a string.
///
/// The macro assumes that the crate follows this structure, and expects the
/// file path to be relative to the `testdata` directory.
///
/// ```text
/// crate_name/
///  ├── src/
///  │   └── lib.rs
///  ├── testdata/
///  │   └── test.txt
///  └── BUILD
/// ```
///
/// ## Example
///
/// ```rust,ignore
/// use oak_file_utils::read_testdata_string;
///
/// let contents = read_testdata_string!("test.txt");
/// ```
#[macro_export]
macro_rules! read_testdata_string {
    ($file:expr) => {{
        let bytes = $crate::read_testdata!($file);
        String::from_utf8(bytes).expect(&format!("testdata file '{}' is not valid UTF-8", $file))
    }};
}

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

/// Support for bazel/blaze style file naming in Cargo tests.
/// Cargo tests run relative to the current directory, so
/// we reset to the workspace root.
#[cfg(not(feature = "bazel"))]
pub fn data_path(path: impl AsRef<Path>) -> PathBuf {
    let mut buf = PathBuf::from(env!("WORKSPACE_ROOT"));
    buf.push(path.as_ref());
    println!("CARGO PATH: {buf:?}");
    buf
}

/// Hack to work around the two different APIs we may encounter for rlocation!
/// -- one returns PathBuf, one returns Option<PathBuf>.
/// Once https://github.com/bazelbuild/rules_rust/issues/2868 is resolved, so
/// that we can update rules_rust, we can remove this.
trait CompatRlocation {
    fn compat_wrap(self) -> Option<PathBuf>;
}

impl CompatRlocation for PathBuf {
    fn compat_wrap(self) -> Option<PathBuf> {
        Some(self)
    }
}

impl CompatRlocation for Option<PathBuf> {
    fn compat_wrap(self) -> Option<PathBuf> {
        self
    }
}

#[cfg(feature = "bazel")]
pub fn data_path(path: impl AsRef<Path>) -> PathBuf {
    const DATA_PATH_PREFIX: &str = "oak";
    let r = runfiles::Runfiles::create().expect("Couldn't initialize runfiles");
    let p = runfiles::rlocation!(r, format!("{DATA_PATH_PREFIX}/{}", path.as_ref().display()))
        .compat_wrap()
        .expect("Couldn't get runfile path");
    if !p.exists() {
        panic!("Data dependency not found: {}", path.as_ref().display());
    }
    p
}

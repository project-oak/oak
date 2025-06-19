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

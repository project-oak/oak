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

#![feature(const_fmt_arguments_new)]
#![feature(async_closure)]

use std::{path::PathBuf, sync::Mutex};

use once_cell::sync::Lazy;

pub mod check_build_licenses;
pub mod check_license;
pub mod check_todo;
pub mod containers;
pub mod examples;
pub mod files;
pub mod internal;
pub mod launcher;
pub mod testing;

pub static PROCESSES: Lazy<Mutex<Vec<i32>>> = Lazy::new(|| Mutex::new(Vec::new()));

// Creates a path relative to the workspace root.
pub fn workspace_path(relative_path: &[&str]) -> PathBuf {
    [&[env!("WORKSPACE_ROOT")], relative_path].concat().iter().collect()
}

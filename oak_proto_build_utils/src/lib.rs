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

use std::fs;

/// Replaces refs to prost with prost_derive. See b/340185847.
/// Only to be called from build scripts of crates that generate prost code.
/// Only to be called when building with Bazel.
/// The issue that this fixes is that prost with "derive" feature uses
/// "prost-derive", which requires std. In Cargo, that works OK as the
/// feature "std" isn't propagated to deps of crates that don't use them,
/// but Bazel's can't handle that. With Bazel, if we bring prost-derive
/// into the index, it'll make deps like `bytes` also use the "std" feature.
/// Take into account that in Cargo, features of dependencies are declared in
/// the "depending" crate, that is, they belong to the dependency arc, while
/// in Bazel, one crate is brought into an index with a fixed set of features.
/// To solve this, and to be able to build for bare metal from Bazel, we
/// import prost without derive to oak_no_std_crates_index, use prost-derive
/// derive macro directly, but we need to change the crate name, as we no
/// longer have prost re-exporting the derive macros.
pub fn fix_prost_derives() -> Result<(), Box<dyn std::error::Error>> {
    // let out_dir_path = std::path::PathBuf::from(std::env::var("OUT_DIR"))?;

    let out_dir = std::env::var("OUT_DIR")?;
    for entry in fs::read_dir(out_dir)? {
        let file_path = entry?.path();
        let contents = fs::read_to_string(&file_path)?;

        let updated = contents.replace("::prost::Message", "::prost_derive::Message");
        let updated = updated.replace("::prost::Oneof", "::prost_derive::Oneof");
        let updated = updated.replace("::prost::Enumeration", "::prost_derive::Enumeration");

        fs::write(&file_path, updated)?;
    }

    Ok(())
}

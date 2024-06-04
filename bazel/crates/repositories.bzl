#
# Copyright 2024 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#
"""
Create the crate repositories needed for Oak.

After being created they need to be loaded.

Usage:

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()
"""

load("@rules_rust//crate_universe:repositories.bzl", "crate_universe_dependencies")
load("//bazel/crates:oak_crates_index.bzl", "oak_crates_index")
load("//bazel/crates:oak_no_std_crates_index.bzl", "oak_no_std_crates_index")

def create_oak_crate_repositories(
        cargo_lockfile = "//:Cargo.bazel.lock",
        lockfile = "//:cargo-bazel-lock.json",
        no_std_cargo_lockfile = "//:Cargo_no_std.bazel.lock",
        no_std_lockfile = "//:cargo-no-std-bazel-lock.json"):
    crate_universe_dependencies(bootstrap = True)
    oak_crates_index(cargo_lockfile, lockfile)
    oak_no_std_crates_index(no_std_cargo_lockfile, no_std_lockfile)

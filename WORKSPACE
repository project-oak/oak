#
# Copyright 2018 The Project Oak Authors
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

workspace(name = "oak")

load("@//bazel:repositories.bzl", "oak_toolchain_repositories")

oak_toolchain_repositories()

load("//bazel/rust:defs.bzl", "setup_rust_dependencies")

setup_rust_dependencies()

load("//bazel/rust:stdlibs.bzl", "setup_rebuilt_rust_stdlibs")

setup_rebuilt_rust_stdlibs()

load("//bazel/crates:patched_crates.bzl", "load_patched_crates")

load_patched_crates()

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()

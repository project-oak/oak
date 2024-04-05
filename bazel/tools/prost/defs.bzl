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
"""Macros to setup the rust proto toolchains."""

load("@prost_toolchain_crates//:defs.bzl", prost_toolchain_crate_repositories = "crate_repositories")
load("@rules_rust//proto/prost:repositories.bzl", "rust_prost_dependencies")
load("@rules_rust//proto/prost:transitive_repositories.bzl", "rust_prost_transitive_repositories")

def setup_prost_toolchain(name = "setup_prost_toolchain"):
    """Setup the toolchain needed for rust_prost_library rules.

    Before calling this from WORKSPACE file, make sure to load the needed dependency crates:

    load("//bazel/tools/prost:deps.bzl", "prost_toolchain_crates")
    prost_toolchain_crates()

    Args:
        name: Not used, but needed for macro-like function to pass linting.
    """

    rust_prost_dependencies()
    rust_prost_transitive_repositories()
    prost_toolchain_crate_repositories()
    native.register_toolchains("//bazel/tools/prost:prost_toolchain")

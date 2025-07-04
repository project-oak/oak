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

load("@rules_rust//crate_universe:defs.bzl", "crates_repository")
load("@rules_rust//crate_universe:repositories.bzl", "crate_universe_dependencies")
load("//bazel/crates:aliasing_crates_repository.bzl", "aliased_crates_repository", "aliasing_crates_repository")
load("//bazel/crates:jemalloc.bzl", "jemalloc_repository")
load("//bazel/crates:oak_crates.bzl", "OAK_NO_STD_ANNOTATIONS", "OAK_NO_STD_CRATES", "OAK_NO_STD_NO_AVX_ANNOTATIONS", "OAK_NO_STD_NO_AVX_CRATES", "OAK_STD_ANNOTATIONS", "OAK_STD_CRATES")
load("//bazel/rust:defs.bzl", "RUST_NIGHTLY_VERSION")

def create_oak_crate_repositories(
        cargo_lockfile = "//:Cargo.bazel.lock",
        lockfile = "//:cargo-bazel-lock.json",
        extra_annotations = {},
        extra_packages = {},
        no_std_cargo_lockfile = "//:Cargo_no_std.bazel.lock",
        no_std_lockfile = "//:cargo-no-std-bazel-lock.json",
        extra_no_std_annotations = {},
        extra_no_std_packages = {},
        no_std_no_avx_cargo_lockfile = "//:Cargo_no_std_no_avx.bazel.lock",
        no_std_no_avx_lockfile = "//:cargo-no-std-no-avx-bazel-lock.json",
        extra_no_std_no_avx_annotations = {},
        extra_no_std_no_avx_packages = {}):
    """ Creates the oak crate repositories.

    Args:
        cargo_lockfile: The cargo lock file for the primary crate index.
        lockfile: The bazel lock file for the primary crate index.
        extra_annotations: Extra annotations to be applied to the primary crate index.
        extra_packages: Extra packages to be added to the primary crate index.
        no_std_cargo_lockfile: The cargo lock file for the no_std crate index.
        no_std_lockfile: The bazel lock file for the no_std crate index.
        extra_no_std_annotations: Extra annotations to be applied to the no_std crate index.
        extra_no_std_packages: Extra packages to be added to the no_std crate index.
        no_std_no_avx_cargo_lockfile: The cargo lock file for the no_std_no_avx crate index.
        no_std_no_avx_lockfile: The bazel lock file for the no_std_no_avx crate index.
        extra_no_std_no_avx_annotations: Extra annotations to be applied to the no_std_no_avx crate index.
        extra_no_std_no_avx_packages: Extra packages to be added to the no_std_no_avx crate index.
    """
    crate_universe_dependencies(bootstrap = True)

    jemalloc_repository()
    crates_repository(
        name = "oak_std_crates_index",
        annotations = OAK_STD_ANNOTATIONS | extra_annotations,
        cargo_lockfile = cargo_lockfile,
        lockfile = lockfile,
        packages = OAK_STD_CRATES | extra_packages,
        rust_version = RUST_NIGHTLY_VERSION,
        supported_platform_triples = [
            "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "x86_64-unknown-none",
        ],
    )

    crates_repository(
        name = "oak_no_std_crates_index",
        annotations = OAK_NO_STD_ANNOTATIONS | extra_no_std_annotations,
        cargo_lockfile = no_std_cargo_lockfile,
        lockfile = no_std_lockfile,
        packages = OAK_NO_STD_CRATES | extra_no_std_packages,
        rust_version = RUST_NIGHTLY_VERSION,
        supported_platform_triples = [
            "aarch64-apple-darwin",
            # Linux for dependencies of build scripts (they run on host):
            "x86_64-unknown-linux-gnu",
            "x86_64-unknown-none",
            "wasm32-unknown-unknown",
        ],
    )
    crates_repository(
        name = "oak_no_std_no_avx_crates_index",
        annotations = OAK_NO_STD_NO_AVX_ANNOTATIONS | extra_no_std_no_avx_annotations,
        cargo_lockfile = no_std_no_avx_cargo_lockfile,
        lockfile = no_std_no_avx_lockfile,
        packages = OAK_NO_STD_NO_AVX_CRATES | extra_no_std_no_avx_packages,
        rust_version = RUST_NIGHTLY_VERSION,
        supported_platform_triples = [
            # Linux for dependencies of build scripts (they run on host):
            "x86_64-unknown-linux-gnu",
            "x86_64-unknown-none",
            "wasm32-unknown-unknown",
        ],
    )

    aliasing_crates_repository(
        name = "oak_crates_index",
        repositories = [
            aliased_crates_repository(
                name = "oak_no_std_crates_index",
                conditions = [Label("//:x86_64-none-setting"), Label("//:wasm32-none-setting")],
                packages = OAK_NO_STD_CRATES.keys() + extra_no_std_packages.keys(),
                # See comment on micro_rpc/BUILD.
                overrides = {
                    "prost-types": Label("@prost_types_oak_patched//:prost-types"),
                    "prost": Label("@prost_types_oak_patched//:prost"),
                },
            ),
            aliased_crates_repository(
                name = "oak_no_std_no_avx_crates_index",
                conditions = [Label("//:x86_64-none-no_avx-setting")],
                packages = OAK_NO_STD_NO_AVX_CRATES.keys() + extra_no_std_no_avx_packages.keys(),
                # See comment on micro_rpc/BUILD.
                overrides = {
                    "prost-types": Label("@prost_types_oak_patched//:prost-types"),
                    "prost": Label("@prost_types_oak_patched//:prost"),
                },
            ),
            aliased_crates_repository(
                name = "oak_std_crates_index",
                conditions = ["//conditions:default"],
                packages = OAK_STD_CRATES.keys() + extra_packages.keys(),
            ),
        ],
    )

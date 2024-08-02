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

load("@rules_rust//crate_universe:defs.bzl", "crate")
load("@rules_rust//crate_universe:repositories.bzl", "crate_universe_dependencies")
load("//bazel/crates:oak_crates_index.bzl", "oak_crates_index")
load("//bazel/crates:oak_no_std_crates_index.bzl", "oak_no_std_crates_index")

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
        extra_no_std_no_avx_annotations = None,
        extra_no_std_no_avx_packages = {}):
    """ Creates the oak crate repositories. 

    Args:
        cargo_lockfile: The cargo lock file for the primary crate index.
        lockfile: The bazel lock file for the primary crate index.
        extra_annotations: Extra annotations to be applied to the primary crate index.
        extra_packages: Extra pakcages to be added to the primary crate index.
        no_std_cargo_lockfile: The cargo lock file for the no_std crate index.
        no_std_lockfile: The bazel lock file for the no_std crate index.
        extra_no_std_annotations: Extra annotations to be applied to the no_std crate index.
        extra_no_std_packages: Extra pakcages to be added to the no_std crate index.
        no_std_no_avx_cargo_lockfile: The cargo lock file for the no_std_no_avx crate index.
        no_std_no_avx_lockfile: The bazel lock file for the no_std_no_avx crate index.
        extra_no_std_no_avx_annotations: Extra annotations to be applied to the no_std_no_avx crate index.
        extra_no_std_no_avx_packages: Extra pakcages to be added to the no_std_no_avx crate index.
    """
    if extra_no_std_no_avx_annotations == None:
        extra_no_std_no_avx_annotations = {}
        extra_no_std_no_avx_annotations |= {
            "sha2": [crate.annotation(
                # Crate feature needed for SHA2 to build if AVX is not enabled.
                crate_features = ["force-soft"],
            )],
        }

    crate_universe_dependencies(bootstrap = True)
    oak_crates_index(
        cargo_lockfile,
        lockfile,
        extra_annotations = extra_annotations,
        extra_packages = extra_packages,
    )
    oak_no_std_crates_index(
        no_std_cargo_lockfile,
        no_std_lockfile,
        extra_annotations = extra_no_std_annotations,
        extra_packages = extra_no_std_packages,
    )
    oak_no_std_crates_index(
        no_std_no_avx_cargo_lockfile,
        no_std_no_avx_lockfile,
        index_name = "oak_no_std_no_avx_crates_index",
        extra_annotations = extra_no_std_no_avx_annotations,
        extra_packages = extra_no_std_no_avx_packages,
    )

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

"""Helpers for loading crates that are patched before use"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_patched_crates():
    _load_patched_prost_types()

def _load_patched_prost_types():
    """Work around rules_rust feature leakage when using prost-types

    prost-types depends on prost with the "derive" feature, which depends on
    prost_derive. prost_derive uses std, but it's only a proc-macro crate, so
    it's only executed at compiled time.

    However, when the rules_rust crate universe tries to resolve feature
    requirements, the need for prost-derive to use std-based crate dependencies
    causes that requirement to be applied unconditionally to those dependent
    crates. This causes no_std builds to fail, because now the dependencies have
    std requirements.

    So what's happening here? Rather than asking rules_rust crate universe to
    pull in prost dependencies, we do it ourselves here.

    We pull in prost-types so that it doesn't attempt to pull prost with the
    prost_derive feature.

    We pull in prost so that we can enable the prost_derive feature without
    telling the crate_universe about it.

    This works for us because `aliasing_crates_repository` that we use to
    automate selection between std/nostd crates also provides for a complete
    target override. Note that if we pulled another crate into the no_std crate
    universe that depends on `prost`, it would *not* get this dependency, so we
    would need to include some more overrides here.

    Note: The `crate.annotation` helper in crates universe provides an
    `override_target` which allows you to replace the rules_rust-generated
    target with any arbitrary target label of your choosing. Unforunately, it
    does not lead to the crate_universe logic skipping the feature resolution
    logic, so the same issue still ends up applying.
    """

    # This must match the version the crates repository uses.
    PROST_VERSION = "0.13.5"

    http_archive(
        name = "prost_types_oak_patched",
        build_file_content = """
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "prost",
    compile_data = ["prost-{prost_version}/prost/README.md"],
    srcs = glob(["prost-{prost_version}/prost/src/**"]),
    deps = ["@oak_crates_index//:bytes"],
    proc_macro_deps = ["@oak_crates_index//:prost-derive"],
    crate_features =["derive", "prost-derive"],
)

rust_library(
    name = "prost-types",
    srcs = glob(["prost-{prost_version}/prost-types/src/*"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        "@oak_crates_index//:prost",
    ],
)
        """.format(prost_version = PROST_VERSION),
        integrity = "sha256-dTNazgva+WrqzjmXkePVN8iPBpyWcACNcu+vKMlL6X0=",
        urls = [
            "https://github.com/tokio-rs/prost/archive/refs/tags/v{}.tar.gz".format(PROST_VERSION),
        ],
    )

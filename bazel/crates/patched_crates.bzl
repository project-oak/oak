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
    """Work around rules_rust proc_macro_deps feature leakage in prost-types

    To solve this, and to be able to build for bare metal from Bazel, we
    import prost without derive to oak_no_std_crates_index, use prost-derive
    derive macro directly, but we need to change the crate name, as we no
    longer have prost re-exporting the derive macros.

    Patch is a workaround for an issue where prost-types pulls in
    prost-derive, triggering a switch to requiring std.

    Why not patch the crate with a crate.annotation? The problem is in the
    generated BUILD files: prost-types pulls in prost with the derive feature
    enabled, and so prost pulls in prost-derive. This is what taints the crate
    universe with the std requirements.

    By pulling in the prost-types subdirectory here, we prevent the rules_rust
    resolution from running on prost-types Cargo.toml, so it never has a chance
    to pull in the invalid prost.

    This patch is coupled with the oak_proto_build_utils::fix_prost_derives
    transforms applied to our generated protos to work around the problems. We
    do this by depending on prost_derive-exported versions of a few types,
    rather than the prost-provided version, which become std-tainted.
    """

    http_archive(
        name = "prost_types_oak_patched",
        build_file_content = """
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "prost-types",
    srcs = glob(["prost-0.12.6/prost-types/src/*"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        "@oak_crates_index//:prost",
    ],
)
        """,
        patch_cmds = [
            "sed -i 's/::prost::Message/::prost_derive::Message/g' prost-0.12.6/prost-types/src/*.rs",
            "sed -i 's/::prost::Oneof/::prost_derive::Oneof/g' prost-0.12.6/prost-types/src/*.rs",
            "sed -i 's/::prost::Enumeration/::prost_derive::Enumeration/g' prost-0.12.6/prost-types/src/*.rs",
        ],
        urls = [
            "https://github.com/tokio-rs/prost/archive/refs/tags/v0.12.6.tar.gz",
        ],
    )

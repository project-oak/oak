#
# Copyright 2025 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "analyze_crate_versions",
    srcs = glob(["*.rs"]),
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:semver",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tree-sitter",
        "@oak_crates_index//:tree-sitter-python",
        "@oak_crates_index//:ureq",
    ],
)

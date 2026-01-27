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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# Example:
# bazel run //tdx_measurement -- \
#  --stage0-rom=$(pwd)/artifacts/binaries/stage0_bin_tdx
rust_binary(
    name = "tdx_measurement",
    srcs = glob(["src/**"]),
    crate_root = "src/main.rs",
    deps = [
        "//stage0_parsing",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_test(
    name = "tdx_measurement_test",
    crate = ":tdx_measurement",
    data = ["@stage0_tdx_bin_for_test//file"],
    deps = [
        "//oak_file_utils",
        "@rules_rust//tools/runfiles",
    ],
)

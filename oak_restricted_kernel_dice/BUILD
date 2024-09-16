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

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel:defs.bzl", "either_platform")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_restricted_kernel_dice",
    srcs = glob(["src/**"]),
    target_compatible_with = either_platform([
        "//:x86_64-linux-setting",  # Needed to run unit tests.
        "//:x86_64-none-no_avx-setting",
        "//:x86_64-none-setting",
    ]),
    deps = [
        "//oak_crypto",
        "//oak_dice",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:hkdf",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:sha2",
    ],
)

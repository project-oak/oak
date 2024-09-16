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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_orchestrator",
    srcs = ["src/main.rs"],
    platform = "//:x86_64-unknown-none",
    deps = [
        "//oak_dice",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_orchestrator",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:log",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

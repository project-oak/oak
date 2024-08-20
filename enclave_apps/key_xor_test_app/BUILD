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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "key_xor_test_app",
    srcs = ["src/main.rs"],
    platform = "//:x86_64-unknown-none",
    deps = [
        "//micro_rpc",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:log",
    ],
)

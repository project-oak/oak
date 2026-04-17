#
# Copyright 2026 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_shared_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_shared_library(
    name = "key_value_lookup_with_json",
    srcs = ["module/lib.rs"],
    platform = "//:wasm32-unknown-unknown",
    deps = [
        "//oak_functions_sdk",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
    ],
)

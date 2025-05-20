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

load("@rules_rust//rust:defs.bzl", "rust_shared_library")
load("@rules_rust_wasm_bindgen//:defs.bzl", "rust_wasm_bindgen")

package(
    licenses = ["notice"],
)

rust_shared_library(
    name = "oak_session_json_lib",
    srcs = ["lib.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    target_compatible_with = ["//:wasm32-none-setting"],
    deps = [
        "@oak//oak_proto_rust",
        "@oak//oak_session",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:wasm-bindgen",
    ],
)

rust_wasm_bindgen(
    name = "oak_session_json_wasm",
    target = "web",
    wasm_file = ":oak_session_json_lib",
)

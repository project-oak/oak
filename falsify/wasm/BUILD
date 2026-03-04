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

rust_binary(
    name = "falsify_wasm",
    srcs = ["main.rs"],
    deps = [
        "//falsify",
        "//falsify/native",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:toml",
    ],
)

rust_test(
    name = "falsify_wasm_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = [
        ":falsify_wasm",
        "//falsify/examples/always_panics:always_panics_wasm",
        "//falsify/examples/no_repeated_bytes:no_repeated_bytes_wasm",
    ],
    env = {
        "FALSIFY_WASM_BIN": "$(rootpath :falsify_wasm)",
        "NO_REPEATED_BYTES_WASM": "$(rootpath //falsify/examples/no_repeated_bytes:no_repeated_bytes_wasm)",
        "ALWAYS_PANICS_WASM": "$(rootpath //falsify/examples/always_panics:always_panics_wasm)",
    },
    deps = [
        "@oak_crates_index//:tempfile",
    ],
)

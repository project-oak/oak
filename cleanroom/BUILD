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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# The cleanroom runner binary. Uses the Oak Functions wasmtime backend
# (lib_unrestricted) to execute sandboxed Wasm modules via the Oak Functions
# ABI, with no host imports exposed to the module.
rust_binary(
    name = "cleanroom",
    srcs = ["src/main.rs"],
    deps = [
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
    ],
)

rust_test(
    name = "cleanroom_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = [
        ":cleanroom",
        "//cleanroom/examples/reverse:reverse_wasm",
        "//cleanroom/examples/to_uppercase:to_uppercase_wasm",
        "//cleanroom/examples/word_count:word_count_wasm",
    ],
    env = {
        "CLEANROOM_BIN": "$(rootpath :cleanroom)",
        "TO_UPPERCASE_WASM": "$(rootpath //cleanroom/examples/to_uppercase:to_uppercase_wasm)",
        "REVERSE_WASM": "$(rootpath //cleanroom/examples/reverse:reverse_wasm)",
        "WORD_COUNT_WASM": "$(rootpath //cleanroom/examples/word_count:word_count_wasm)",
    },
    deps = [
        "@oak_crates_index//:tempfile",
    ],
)

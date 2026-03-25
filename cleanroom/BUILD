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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

filegroup(
    name = "wit_files",
    srcs = ["wit/cleanroom-ifc.wit"],
    visibility = ["//visibility:public"],
)

# The cleanroom runner binary. Supports three modes:
#
# - `cleanroom server`: IFC-enforcing daemon listening on a Unix socket.
# - `cleanroom client`: Client used inside the container.
# - `cleanroom shell`:  Launch a network-isolated container with the client.
rust_library(
    name = "cleanroom_lib",
    srcs = [
        "src/client.rs",
        "src/ifc.rs",
        "src/lib.rs",
        "src/policy.rs",
        "src/protocol.rs",
        "src/server.rs",
        "src/shell.rs",
        "src/wasi_ifc.rs",
    ],
    compile_data = [
        "wit/cleanroom-ifc.wit",
    ],
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bincode",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:http",
        "@oak_crates_index//:log",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tempfile",
        "@oak_crates_index//:toml",
        "@oak_crates_index//:wasmtime",
        "@oak_crates_index//:wasmtime-wasi",
        "@oak_crates_index//:wasmtime-wasi-http",
    ],
)

rust_binary(
    name = "cleanroom",
    srcs = ["src/bin/main.rs"],
    deps = [
        ":cleanroom_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
    ],
)

rust_test(
    name = "cleanroom_lib_test",
    crate = ":cleanroom_lib",
)

rust_test(
    name = "cleanroom_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = [
        ":cleanroom",
        "//cleanroom/examples/cat_file:cat_file_wasm",
        "//cleanroom/examples/reverse:reverse_wasm",
        "//cleanroom/examples/to_uppercase:to_uppercase_wasm",
        "//cleanroom/examples/word_count:word_count_wasm",
    ],
    env = {
        "CLEANROOM_BIN": "$(rootpath :cleanroom)",
        "CAT_FILE_WASM": "$(rootpath //cleanroom/examples/cat_file:cat_file_wasm)",
        "TO_UPPERCASE_WASM": "$(rootpath //cleanroom/examples/to_uppercase:to_uppercase_wasm)",
        "REVERSE_WASM": "$(rootpath //cleanroom/examples/reverse:reverse_wasm)",
        "WORD_COUNT_WASM": "$(rootpath //cleanroom/examples/word_count:word_count_wasm)",
    },
    deps = [
        ":cleanroom_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bincode",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tempfile",
    ],
)

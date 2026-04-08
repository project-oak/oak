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
load("//cleanroom:wasi_binary.bzl", "wasi_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# A standalone replacement for `cargo vendor`. Compiles to wasm32-wasip2
# and runs inside the cleanroom sandbox with IFC-aware I/O.
#
# Reads a JSON config from stdin, downloads all registry crate archives from
# crates.io, extracts them into a vendor/ directory via the filesystem proxy,
# and generates the .cargo/config.toml needed for offline builds.
rust_binary(
    name = "crate_vendor_bin",
    srcs = ["src/main.rs"],
    deps = [
        "//cleanroom/sdk:cleanroom_sdk",
        "//util/digest:oak_digest",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:flate2",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:toml",
    ],
)

wasi_binary(
    name = "crate_vendor",
    binary = ":crate_vendor_bin",
)

# End-to-end integration test. Downloads actual crates from crates.io
# and verifies the output structure, checksums, and config generation.
# Requires network access.
rust_test(
    name = "crate_vendor_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = [
        "testdata/Cargo.lock",
        ":crate_vendor",
        "//cleanroom",
    ],
    env = {
        "CLEANROOM_BIN": "$(rootpath //cleanroom:cleanroom)",
        "CRATE_VENDOR_WASM": "$(rootpath :crate_vendor)",
        "TEST_CARGO_LOCK": "$(rootpath testdata/Cargo.lock)",
    },
    tags = [
        "manual",
        "requires-network",
    ],
    deps = [
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tempfile",
    ],
)

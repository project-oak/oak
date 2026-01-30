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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "tessera",
    srcs = glob(["**/*.rs"]),
    deps = [
        "//util/digest:oak_digest",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:ed25519-dalek",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:thiserror",
    ],
)

rust_test(
    name = "tessera_tests",
    compile_data = [
        "testdata/test.tlog-proof",
    ],
    crate = ":tessera",
)

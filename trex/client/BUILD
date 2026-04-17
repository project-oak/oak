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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "client",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "trex_client",
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_time",
        "//tr/endorscope",
        "//tr/intoto",
        "//tr/rekor",
        "//trex/cosign_util",
        "//util/digest:oak_digest",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:log",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:reqwest",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tempfile",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:url",
    ],
)

rust_test(
    name = "client_test",
    crate = ":client",
)

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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_proxy_lib",
    srcs = glob(["src/**/*.rs"], exclude = ["src/tests.rs"]),
    deps = [
        "//oak_attestation",
        "//oak_attestation_gcp",
        "//oak_attestation_verification",
        "//oak_proto_rust",
        "//oak_session",
        "//oak_time",
        "//oak_time:oak_time_std",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:humantime-serde",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-tungstenite",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:toml",
        "@oak_crates_index//:tungstenite",
        "@oak_crates_index//:url",
        "@oak_crates_index//:x509-cert",
    ],
)

rust_test(
    name = "oak_proxy_lib_tests",
    srcs = ["src/tests.rs"],
    data = [
        "//oak_proxy/testdata",
    ],
    deps = [
        ":oak_proxy_lib",
        "@oak_crates_index//:toml",
    ],
)

rust_test(
    name = "oak_proxy_lib_unit_tests",
    crate = ":oak_proxy_lib",
    deps = [
        "@oak_crates_index//:rand", 
        "@oak_crates_index//:tempfile",
    ],
)

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
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "c2sp",
    srcs = glob(["**/*.rs"]),
    # ML-DSA-44 support requires the Tink C++ FFI, which depends on a C++
    # runtime and is therefore only available on Linux.  On bare-metal targets
    # (x86_64-unknown-none) the feature is absent and all ML-DSA code paths
    # are compiled out.
    crate_features = select({
        "//:x86_64-linux-setting": ["ml_dsa"],
        "//conditions:default": [],
    }),
    deps = [
        "//oak_proto_rust",
        "//oak_time",
        "//util/digest:oak_digest",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:ed25519-dalek",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:rs_merkle",
        "@oak_crates_index//:thiserror",
    ] + select({
        "//:x86_64-linux-setting": ["//oak_crypto:oak_crypto_tink"],
        "//conditions:default": [],
    }),
)

rust_test(
    name = "c2sp_tests",
    compile_data = [
        "testdata/test.tlog-proof",
    ],
    crate = ":c2sp",
    crate_features = ["ml_dsa"],
    target_compatible_with = ["@platforms//os:linux"],
)

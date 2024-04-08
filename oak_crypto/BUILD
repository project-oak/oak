#
# Copyright 2024 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_crypto",
    srcs = glob([
        "src/*.rs",
        "src/hpke/*.rs",
        "src/noise_handshake/*.rs",
    ]),
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:aes-gcm",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:hkdf",
        "@oak_crates_index//:hpke",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:pkcs8",
        "@oak_crates_index//:primeorder",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:zeroize",
    ],
)

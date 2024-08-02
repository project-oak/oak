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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//bazel:defs.bzl", "either_platform", "select_std_crates")

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
    target_compatible_with = either_platform([
        "//:x86_64-linux-setting",
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
    ]),
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:static_assertions",
    ] + select_std_crates([
        "aead",
        "aes-gcm",
        "anyhow",  # oak_client requires stdful version.
        "ecdsa",
        "hkdf",
        "hpke",
        "p256",  # oak_containers_orchestrator requires stdful version.
        "pkcs8",
        "primeorder",
        "rand_chacha",
        "rand_core",
        "sha2",
        "zeroize",
    ]),
)

rust_test(
    name = "oak_crypto_test",
    size = "small",
    crate = ":oak_crypto",
    deps = [
        "@oak_crates_index//:hex",
        "@oak_crates_index//:tokio",
    ],
)

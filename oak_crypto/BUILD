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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_crypto_tink",
    srcs = glob([
        "src/tink/*.rs",
    ]),
    deps = [
        ":oak_crypto",
        "//cc/crypto/tink/signature:verification-ffi",
        "//oak_ffi:cxx_string",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:static_assertions",
    ],
)

rust_library(
    name = "oak_crypto",
    srcs = glob([
        "src/*.rs",
        "src/certificate/*.rs",
        "src/hpke/*.rs",
        "src/noise_handshake/*.rs",
    ]),
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_proto_rust",
        "//oak_time",
        "@oak_crates_index//:aead",
        "@oak_crates_index//:aes-gcm",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:hkdf",
        "@oak_crates_index//:hpke",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:pkcs8",
        "@oak_crates_index//:primeorder",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_chacha",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:thiserror",
        "@oak_crates_index//:zeroize",
    ],
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

rust_test(
    name = "oak_crypto_tink_test",
    size = "small",
    crate = ":oak_crypto_tink",
    data =
        [
            "//cc/crypto/tink/signature/testdata:message",
            "//cc/crypto/tink/signature/testdata:public_keyset",
            "//cc/crypto/tink/signature/testdata:signature",
        ],
    deps = [
        "//oak_file_utils",
    ],
)

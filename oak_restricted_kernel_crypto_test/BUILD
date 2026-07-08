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

load("@rules_rust//rust:defs.bzl", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

_TEST_SRCS = [
    "src/tests.rs",
    "src/wycheproof.rs",
]

_COMMON_DATA = [
    "//enclave_apps/oak_orchestrator",
    "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    "//stage0_bin",
    "//third_party/wycheproof:aead_test_vectors",
]

_TEST_DEPS = [
    "//micro_rpc",
    "//oak_file_utils",
    "//oak_launcher_utils",
    "//oak_restricted_kernel_crypto_test/proto:service",
    "@oak_crates_index//:env_logger",
    "@oak_crates_index//:hex",
    "@oak_crates_index//:log",
    "@oak_crates_index//:serde",
    "@oak_crates_index//:serde_json",
    "@oak_crates_index//:tokio",
    "@oak_crates_index//:which",
]

# Test exercising AEAD operations using the aes-gcm enclave app.
rust_test(
    name = "tests",
    srcs = _TEST_SRCS,
    data = _COMMON_DATA + [
        "//oak_restricted_kernel_crypto_test/enclave_app",
    ],
    rustc_env = {
        "ENCLAVE_APP_PATH": "oak_restricted_kernel_crypto_test/enclave_app/enclave_app",
    },
    target_compatible_with = ["@platforms//os:linux"],
    deps = _TEST_DEPS,
)

# Test exercising AEAD operations using the BoringSSL enclave app.
rust_test(
    name = "boringssl_tests",
    srcs = _TEST_SRCS,
    crate_root = "src/tests.rs",
    data = _COMMON_DATA + [
        "//oak_restricted_kernel_crypto_test/enclave_app_boringssl",
    ],
    rustc_env = {
        "ENCLAVE_APP_PATH": "oak_restricted_kernel_crypto_test/enclave_app_boringssl/enclave_app_boringssl",
    },
    target_compatible_with = ["@platforms//os:linux"],
    deps = _TEST_DEPS,
)

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

rust_test(
    name = "tests",
    srcs = [
        "src/tests.rs",
        "src/wycheproof.rs",
    ],
    data = [
        "//enclave_apps/oak_orchestrator",
        "//oak_restricted_kernel_crypto_test/enclave_app",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
        "//third_party/wycheproof:aead_test_vectors",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//micro_rpc",
        "//oak_file_utils",
        "//oak_launcher_utils",
        "//oak_restricted_kernel_crypto_test/proto:service",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:which",
    ],
)

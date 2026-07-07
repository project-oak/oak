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

# End-to-end test of the Oak LLVM libc port: boots the FFI test app enclave
# binary under Oak Restricted Kernel and checks its serial output.
rust_test(
    name = "integration_test",
    srcs = ["integration_test.rs"],
    data = [
        "//oak_enclave_runtime_support/tests/libc/app:oak_ffi_test_app",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_bin",
        "//stage0_bin",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_file_utils",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:which",
    ],
)

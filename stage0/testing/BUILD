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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "test_kernel",
    srcs = [
        "test_kernel.rs",
    ],
    compile_data = ["boot.s"],
    linker_script = "//oak_restricted_kernel:layout.ld",
    # Use `firmware` instead of `unknown-none` as we don't set up SSE/AVX.
    platform = "//:x86_64-firmware",
    tags = ["no-clippy"],
    deps = [
        "//oak_linux_boot_params",
        "@oak_crates_index//:log",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:uart_16550",
        "@oak_crates_index//:x86_64",
    ],
)

rust_test(
    name = "stage0_kernel_test",
    srcs = [
        "test_kernel_test.rs",
    ],
    data = [
        "//oak_restricted_kernel_wrapper:stage0_test_kernel_bin",
        "//stage0_bin",
    ],
    deps = [
        "//oak_file_utils",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:which",
    ],
)

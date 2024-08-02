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
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_restricted_kernel_wrapper_virtio_console_channel",
    srcs = glob(["src/**/*.rs"]),
    compile_data = ["src/asm/boot.s"],
    crate_features = ["bazel"],  # TODO: b/333064338 remove.
    data = [
        "//oak_restricted_kernel_bin:oak_restricted_kernel_bin_virtio_console_channel",
    ],
    features = ["no_libstdcxx"],  # See https://github.com/f0rmiga/gcc-toolchain/blob/0.4.2/docs/README.md
    linker_script = ":layout.ld",
    platform = "//:x86_64-unknown-none-noavx-softfloat",
    rustc_env = {
        "PAYLOAD_PATH": "$(location //oak_restricted_kernel_bin:oak_restricted_kernel_bin_virtio_console_channel)",
    },
    rustc_flags = [
        "-C",
        "relocation-model=pie",
    ],
    deps = [
        "@//oak_linux_boot_params",
        "@oak_no_std_crates_index//:elf",
        "@oak_no_std_crates_index//:x86_64",
    ],
)

rust_binary(
    name = "oak_restricted_kernel_wrapper_simple_io_channel",
    srcs = glob(["src/**/*.rs"]),
    compile_data = ["src/asm/boot.s"],
    crate_features = ["bazel"],  # TODO: b/333064338 remove.
    data = [
        "//oak_restricted_kernel_bin:oak_restricted_kernel_bin_simple_io_channel",
    ],
    features = ["no_libstdcxx"],  # See https://github.com/f0rmiga/gcc-toolchain/blob/0.4.2/docs/README.md
    linker_script = ":layout.ld",
    platform = "//:x86_64-unknown-none-noavx-softfloat",
    rustc_env = {
        "PAYLOAD_PATH": "$(location //oak_restricted_kernel_bin:oak_restricted_kernel_bin_simple_io_channel)",
    },
    rustc_flags = [
        "-C",
        "relocation-model=pie",
    ],
    deps = [
        "@//oak_linux_boot_params",
        "@oak_no_std_crates_index//:elf",
        "@oak_no_std_crates_index//:x86_64",
    ],
)

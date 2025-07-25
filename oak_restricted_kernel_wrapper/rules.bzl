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
"""Rule to build Restricted Kernel wrapped in a bzImage container."""

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//bazel:defs.bzl", "objcopy")
load("//oak_kernel_measurement:rules.bzl", "kernel_measurement")

_RK_WRAPPER_RUSTC_FLAGS = [
    "--codegen=lto=true",  # Enable https://llvm.org/docs/LinkTimeOptimization.html.
    "--codegen=panic=abort",
    "--codegen=relocation-model=dynamic-no-pic",
    "--codegen=opt-level=z",  # Optimize for binary size, but also turn off loop vectorization.
]

def kernel_bzimage_and_measurements(name, payload, visibility = None):
    rust_binary(
        name = name,
        srcs = native.glob(["src/**/*.rs"]),
        compile_data = [
            "src/asm/boot.s",
            payload,
        ],
        linker_script = ":layout.ld",
        platform = "//:x86_64-unknown-none-noavx",
        rustc_env = {
            "PAYLOAD_PATH": "$(location " + payload + ")",
        },
        rustc_flags = _RK_WRAPPER_RUSTC_FLAGS,
        deps = [
            "@//oak_linux_boot_params",
            "@oak_crates_index//:elf",
            "@oak_crates_index//:x86_64",
        ],
        visibility = ["//visibility:private"],
    )

    objcopy(
        name = name + "_bin",
        src = ":" + name,
    )

    kernel_measurement(
        name = name + "_measurement",
        src = ":" + name + "_bin",
    )

    native.filegroup(
        name = name + "_files",
        srcs = [
            ":" + name + "_bin",
            ":" + name + "_measurement",
        ],
        visibility = visibility,
    )

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

load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

cc_library(
    name = "ffi_demo_cc",
    srcs = ["cc/ffi_demo.c"],
    hdrs = ["cc/ffi_demo.h"],
    copts = ["-ffreestanding"],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    deps = [
        "//third_party/llvm_libc",
    ],
)

rust_binary(
    name = "oak_ffi_test_app",
    srcs = ["src/main.rs"],
    platform = "//:x86_64-unknown-none",
    rustc_flags = [
        "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        ":ffi_demo_cc",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:log",
    ],
)

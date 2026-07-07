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
    name = "cxx_demo_cc",
    srcs = ["cc/cxx_demo.cc"],
    hdrs = ["cc/cxx_demo.h"],
    copts = [
        "-ffreestanding",
        "-fno-exceptions",
        "-fno-rtti",
        "-nostdinc++",
        "-nostdlibinc",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    deps = [
        "//third_party/llvm_libc:llvm_libcxx",
    ],
)

rust_binary(
    name = "oak_cxx_test_app",
    srcs = ["src/main.rs"],
    platform = "//:x86_64-unknown-none",
    rustc_flags = [
        "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        ":cxx_demo_cc",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:log",
    ],
)

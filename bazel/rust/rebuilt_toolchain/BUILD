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

# This package creates a sysroot for a new toolchain where the Rust std
# libraries have been rebuilt with different flags.

load("@rules_rust//rust:defs.bzl", "rust_stdlib_filegroup")
load("@rules_rust//rust:toolchain.bzl", "rust_toolchain")
load("//bazel/rust:defs.bzl", "RUST_EDITION")
load(":defs.bzl", "toolchain_sysroot", "with_stdlib_build")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# Rebuild stdlibs for a new toolchain. This uses a different toolchain to
# rebuild the libraries from sources, since the curent toolchain being built
# is not yet available.
with_stdlib_build(
    name = "stdlibs_build",
    srcs = ["@stdlibs//:stdlib_sources"],
)

rust_stdlib_filegroup(
    name = "rust_stdlibs",
    srcs = [":sysroot_with_stdlibs"],
)

toolchain_sysroot(
    name = "sysroot_with_stdlibs",
    srcs = [
        ":stdlibs_build",
    ],
    dirname = "sysroot_with_stdlibs",
    target_triple = "x86_64-unknown-none",
)

rust_toolchain(
    name = "toolchain_rebuilt_x86_64-unknown-none_impl",
    binary_ext = "",
    default_edition = RUST_EDITION,
    dylib_ext = ".so",
    exec_triple = "x86_64-unknown-linux-gnu",
    extra_rustc_flags = [
        "--codegen=linker-flavor=gcc",
        "--codegen=relocation-model=static",
        "--codegen=code-model=large",
        "--codegen=target-feature=+rdrand",
        "--codegen=opt-level=z",
        "--cfg=aes_force_soft",
        "--cfg=polyval_force_soft",
    ],
    rust_doc = "@rust_toolchain_repo__x86_64-unknown-none__nightly_tools//:rustdoc",
    rust_std = ":rust_stdlibs",
    rustc = "@rust_toolchain_repo__x86_64-unknown-none__nightly_tools//:rustc",
    rustc_lib = "@rust_toolchain_repo__x86_64-unknown-none__nightly_tools//:rustc_lib",
    staticlib_ext = ".a",
    stdlib_linkflags = [],
    target_triple = "x86_64-unknown-none",
)

toolchain(
    name = "toolchain_rebuilt_x86_64-unknown-none",
    exec_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:linux",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
        "//bazel/rust:avx_OFF",
        "//bazel/rust:code_model_LARGE",
    ],
    toolchain = ":toolchain_rebuilt_x86_64-unknown-none_impl",
    toolchain_type = "@rules_rust//rust:toolchain_type",
)

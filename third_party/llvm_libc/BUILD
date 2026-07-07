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

load("@aspect_bazel_lib//lib:copy_to_directory.bzl", "copy_to_directory")
load("@rules_foreign_cc//foreign_cc:defs.bzl", "cmake")

package(default_visibility = ["//visibility:public"])

exports_files(["BUILD.llvm_libc"])

# Oak-specific source files that are added on top of the upstream LLVM libc
# source tree. These are checked in (rather than carried as patches) because
# they only add new files; keeping them as normal files makes them easy to
# review and modify. Each file lives at overlay/<path> where <path> is its
# destination within the LLVM source tree (e.g. overlay/libc/config/oak/...
# lands at libc/config/oak/...).
filegroup(
    name = "oak_overlay",
    srcs = glob(["overlay/**"]),
)

# Merge the upstream archive with the Oak overlay into a single source tree
# that the CMake build can consume.
#
# - Files from the `@llvm_libc_src` archive keep their in-archive paths (the
#   `external/<repo>` prefix is stripped via `include_external_repositories`).
# - Overlay files have their `overlay/` prefix stripped via `replace_prefixes`
#   so they land at the corresponding location in the LLVM source tree.
#
# `hardlink = "on"` avoids physically duplicating the (very large) archive.
copy_to_directory(
    name = "llvm_libc_source",
    srcs = [
        ":oak_overlay",
        "@llvm_libc_src//:llvm_libc_srcs",
    ],
    hardlink = "on",
    include_external_repositories = ["*llvm_libc_src*"],
    replace_prefixes = {"overlay/": ""},
)

# Stage the vendored PyYAML pure-Python sources into a single directory whose
# root is a valid `PYTHONPATH` entry (i.e. it contains the `yaml/` package).
# The LLVM libc header generator (hdrgen) imports `yaml`; see the `env`
# attribute of the `cmake` rule below and //MODULE.bazel (@pyyaml_src).
copy_to_directory(
    name = "pyyaml_site_packages",
    srcs = ["@pyyaml_src//:lib"],
    hardlink = "on",
    include_external_repositories = ["*pyyaml_src*"],
)

cmake(
    name = "llvm_libc",
    build_args = ["-j4"],
    cache_entries = {
        "CMAKE_SYSTEM_NAME": "Generic",
        "CMAKE_SYSTEM_PROCESSOR": "x86_64",
        "LLVM_ENABLE_RUNTIMES": "libc",
        "LLVM_LIBC_FULL_BUILD": "ON",
        # The target triple selects the Oak OS: cmake derives LIBC_TARGET_OS
        # ("oak") from the triple, which in turn selects the libc/config/oak
        # config and the src/.../oak implementations. No OS override needed.
        "LIBC_TARGET_TRIPLE": "x86_64-unknown-oak-elf",
        "CMAKE_BUILD_TYPE": "Release",
        "LLVM_INCLUDE_TESTS": "OFF",
        "LLVM_INCLUDE_BENCHMARKS": "OFF",
        # rules_foreign_cc injects '-stdlib=libstdc++' from the host
        # toolchain, which is invalid for a freestanding target and triggers
        # -Werror,-Wunused-command-line-argument.
        "CMAKE_C_FLAGS": "-Wno-unused-command-line-argument",
        "CMAKE_CXX_FLAGS": "-Wno-unused-command-line-argument",
    },
    # The LLVM libc header generator (hdrgen) imports pyyaml and calls
    # `yaml.safe_load`, but the Python cmake finds in the Bazel sandbox does
    # not have pyyaml on its default sys.path. We stage a vendored, hermetic
    # copy (see the `:pyyaml_site_packages` directory and @pyyaml_src in
    # //MODULE.bazel) and put it on PYTHONPATH. `$$EXT_BUILD_ROOT$$` is
    # substituted by rules_foreign_cc with the absolute sandbox root at build
    # time, and `$(execpath)` resolves to the staged directory.
    build_data = [":pyyaml_site_packages"],
    env = {
        "PYTHONPATH": "$$EXT_BUILD_ROOT$$/$(execpath :pyyaml_site_packages)",
    },
    lib_source = ":llvm_libc_source",
    # LLVM libc installs to lib/<target-triple>/ when LIBC_TARGET_TRIPLE
    # is set. rules_foreign_cc resolves these relative to the install
    # prefix's lib/ directory.
    #
    # Note: libm.a is built (to satisfy the cmake install step) but not
    # exported here because oak_enclave_runtime_support already provides
    # the required math symbols (fmod, log2, round, sqrtf, etc.).
    out_static_libs = [
        "x86_64-unknown-oak-elf/libc.a",
    ],
    targets = [
        "libc",
        "libm",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    # rules_foreign_cc's `detect_root` returns the *parent* of a
    # `copy_to_directory` tree artifact, so the working directory must be
    # prefixed with the tree artifact's basename (i.e. this target's name,
    # "llvm_libc_source") to reach the merged source tree's `runtimes/`
    # directory, which drives the LLVM_ENABLE_RUNTIMES build.
    working_directory = "llvm_libc_source/runtimes",
)

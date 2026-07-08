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
load("@rules_cc//cc:cc_library.bzl", "cc_library")
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

# Stage the (small, checked-in) Oak overlay into its own tree, *copying* the
# files rather than hardlinking them.
#
# copy_to_directory's `hardlink = "on"` makes each output file share an inode
# with its source; because bazel marks action outputs read-only/executable,
# hardlinking the checked-in overlay files flips their permissions in the
# workspace too (git/jj then reports a spurious `100644 -> 100755` change).
# `hardlink = "off"` copies instead, so the workspace files are never touched.
# The overlay is tiny (~220KB), so copying is cheap. See the aspect_bazel_lib
# `hardlink` docs ("hardlinks to source files are not recommended"):
# https://github.com/aspect-build/bazel-lib/blob/main/docs/copy_to_directory.md
copy_to_directory(
    name = "oak_overlay_staged",
    srcs = [":oak_overlay"],
    # Strip the `overlay/` prefix so files land at their destination within the
    # LLVM source tree (e.g. overlay/libc/config/oak/... -> libc/config/oak/...).
    hardlink = "off",
    replace_prefixes = {"overlay/": ""},
)

# Merge the upstream archive with the staged Oak overlay into a single source
# tree that the CMake build can consume.
#
# - Files from the `@llvm_libc_src` archive keep their in-archive paths (the
#   `external/<repo>` prefix is stripped via `include_external_repositories`).
# - `:oak_overlay_staged` already has its `overlay/` prefix stripped, but as a
#   tree artifact its files arrive under an `oak_overlay_staged/` directory,
#   which `replace_prefixes` strips so they land at their real destinations
#   (e.g. `libc/config/oak/...`).
#
# `hardlink = "on"` avoids physically duplicating the (very large, ~2.4GB)
# archive: its files are hardlinked from bazel's external cache and the staged
# overlay from bazel-out. Neither is a checked-in workspace file, so the
# permission-bleed problem described on `:oak_overlay_staged` does not apply.
copy_to_directory(
    name = "llvm_libc_source",
    srcs = [
        ":oak_overlay_staged",
        "@llvm_libc_src//:llvm_libc_srcs",
    ],
    hardlink = "on",
    include_external_repositories = ["*llvm_libc_src*"],
    replace_prefixes = {"oak_overlay_staged/": ""},
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
    build_data = [
        ":llvm_libc_source",
        ":pyyaml_site_packages",
    ],
    env = {
        "PYTHONPATH": "$$EXT_BUILD_ROOT$$/$(execpath :pyyaml_site_packages)",
    },
    # Copy two Oak-specific headers into the install tree that the default
    # install step does not ship, so the installed headers are self-consistent
    # for any C/C++ consumer of the Oak libc (in particular libc++; see the
    # `llvm_libcxx` target below):
    #
    # - `llvm-libc-macros/baremetal/time-macros.h`: the generic installed
    #   `llvm-libc-macros/time-macros.h` selects this variant for ELF targets
    #   (which the Oak triple is), e.g. for libc++'s `<chrono>`.
    # - `bits/types/mbstate_t.h`: an Oak overlay shim (not a generated public
    #   header, hence not installed by default) that libc++ needs; see that
    #   file for details. Installing it here puts it on the same include path as
    #   the generated libc headers.
    postfix_script = " && ".join([
        "mkdir -p $$INSTALLDIR/include/llvm-libc-macros/baremetal",
        "cp $$EXT_BUILD_ROOT/$(execpath :llvm_libc_source)/libc/include/llvm-libc-macros/baremetal/time-macros.h $$INSTALLDIR/include/llvm-libc-macros/baremetal/",
        "mkdir -p $$INSTALLDIR/include/bits/types",
        "cp $$EXT_BUILD_ROOT/$(execpath :llvm_libc_source)/libc/include/bits/types/mbstate_t.h $$INSTALLDIR/include/bits/types/",
    ]),
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

# LLVM libc++ built for Oak Restricted Kernel.
#
# libc++ is built together with libc++abi in a single runtimes invocation
# (LLVM_ENABLE_RUNTIMES=libcxx;libcxxabi) so libc++ finds the libc++abi headers
# in-tree. libc++abi supplies the C++ ABI runtime the compiler and libc++
# expect: `operator new`/`delete`, `__cxa_*`, and guard variables.
#
# libc++abi is configured for a freestanding, single-threaded enclave:
#   - No exceptions and no LLVM unwinder (no unwind / signal support)
#   - No threads (Restricted Kernel is single-threaded; guard variables become
#     trivial)
#   - Baremetal mode (drops the fprintf/demangling-based abort diagnostics)
# libc++ itself additionally disables:
#   - RTTI (requires dynamic linking support)
#   - filesystem, locale, random device, time zone database
#   - shared libraries (static linking only)
#
# Two runtime-support symbols that libc++abi does not own (`__dso_handle` and
# `__cxa_atexit`) are supplied by `oak_enclave_runtime_support` (in Rust,
# alongside the `__llvm_libc_*` vendor callbacks); an enclave app never returns,
# so static destructors registered via `__cxa_atexit` need never run.
cmake(
    name = "llvm_libcxx",
    build_args = ["-j4"],
    build_data = [
        ":pyyaml_site_packages",
    ],
    cache_entries = {
        "CMAKE_SYSTEM_NAME": "Generic",
        "CMAKE_SYSTEM_PROCESSOR": "x86_64",
        "LLVM_ENABLE_RUNTIMES": "libcxx;libcxxabi",
        "CMAKE_BUILD_TYPE": "Release",
        "LLVM_INCLUDE_TESTS": "OFF",
        "LLVM_INCLUDE_BENCHMARKS": "OFF",
        # -nostdlibinc: remove host /usr/include (glibc) but keep clang
        # builtins (stddef.h, stdarg.h, etc.).
        #
        # Include path: the LLVM libc headers installed by the `:llvm_libc` dep
        # (available under `$EXT_BUILD_DEPS`). This tree includes the Oak
        # overlay's `bits/types/mbstate_t.h` shim, which `:llvm_libc` stages
        # into its install dir (see that target's `postfix_script`).
        #
        # -nostdinc++: remove host libstdc++ headers; CMake adds the libc++
        # headers it is building automatically.
        "CMAKE_C_FLAGS": "-Wno-unused-command-line-argument -nostdlibinc -isystem $${EXT_BUILD_DEPS}/llvm_libc/include",
        "CMAKE_CXX_FLAGS": "-Wno-unused-command-line-argument -nostdlibinc -nostdinc++ -isystem $${EXT_BUILD_DEPS}/llvm_libc/include",
        # --- libc++ configuration ---
        "LIBCXX_ENABLE_SHARED": "OFF",
        "LIBCXX_ENABLE_STATIC": "ON",
        "LIBCXX_ENABLE_EXCEPTIONS": "OFF",
        "LIBCXX_ENABLE_RTTI": "OFF",
        "LIBCXX_ENABLE_THREADS": "OFF",
        "LIBCXX_ENABLE_MONOTONIC_CLOCK": "OFF",
        "LIBCXX_ENABLE_FILESYSTEM": "OFF",
        "LIBCXX_ENABLE_RANDOM_DEVICE": "OFF",
        "LIBCXX_ENABLE_LOCALIZATION": "OFF",
        "LIBCXX_ENABLE_UNICODE": "OFF",
        "LIBCXX_ENABLE_WIDE_CHARACTERS": "OFF",
        "LIBCXX_ENABLE_TIME_ZONE_DATABASE": "OFF",
        "LIBCXX_HAS_TERMINAL_AVAILABLE": "OFF",
        "LIBCXX_INCLUDE_TESTS": "OFF",
        "LIBCXX_INCLUDE_BENCHMARKS": "OFF",
        "LIBCXX_CXX_ABI": "libcxxabi",
        # --- libc++abi configuration ---
        "LIBCXXABI_ENABLE_SHARED": "OFF",
        "LIBCXXABI_ENABLE_STATIC": "ON",
        # No exceptions: builds the no-op cxa_noexception.cpp variants.
        "LIBCXXABI_ENABLE_EXCEPTIONS": "OFF",
        # No unwinder dependency (we have no libunwind).
        "LIBCXXABI_USE_LLVM_UNWINDER": "OFF",
        # Single-threaded: guard variables need no atomics/locks.
        "LIBCXXABI_ENABLE_THREADS": "OFF",
        # Baremetal: avoids the fprintf/stderr-based abort diagnostics path.
        "LIBCXXABI_BAREMETAL": "ON",
        # Provide operator new/delete from libc++abi.
        "LIBCXXABI_ENABLE_NEW_DELETE_DEFINITIONS": "ON",
        # Keep the demangler out of std::terminate to shrink the binary.
        "LIBCXXABI_NON_DEMANGLING_TERMINATE": "ON",
    },
    # See the `llvm_libc` target for why PyYAML is staged on PYTHONPATH.
    env = {
        "PYTHONPATH": "$$EXT_BUILD_ROOT$$/$(execpath :pyyaml_site_packages)",
    },
    lib_source = ":llvm_libc_source",
    # The default cmake install step copies all three static archives into
    # `lib/` and the assembled headers into `include/c++/v1`, so no manual
    # postfix copy is needed.
    out_include_dir = "include/c++/v1",
    out_static_libs = [
        "libc++.a",
        "libc++abi.a",
        "libc++experimental.a",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    # `cxx` is a meta-target that builds the libc++ static library plus
    # libc++experimental.a; the PSTL and time-zone-database sources are excluded
    # by our feature flags. `cxxabi_static` and `generate-cxx-headers` are not
    # pulled in by `cxx`, so they are listed explicitly.
    targets = [
        "generate-cxx-headers",
        "cxxabi_static",
        "cxx",
    ],
    deps = [":llvm_libc"],
    # See the `llvm_libc` target for why the working directory is prefixed with
    # the merged source tree's basename.
    working_directory = "llvm_libc_source/runtimes",
)


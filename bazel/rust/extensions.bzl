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

"""Module extensions for Rust toolchains."""

load("@rules_rust//rust:repositories.bzl", "rust_repository_set")
load("//bazel/rust:defs.bzl", "RUST_EDITION", "RUST_NIGHTLY_DATE", "RUST_SHA256S", "RUST_VERSIONS", "STDLIBS_SHA256", "SUPPORTED_HOST_TRIPLES", "SUPPORTED_RUST_COMPONENTS", "SUPPORTED_TARGET_TRIPLES")
load("//bazel/rust:stdlibs.bzl", "stdlibs")

def _ensure_hashes():
    """Validate that all required Rust toolchain hashes are present and consistent."""

    # If a hash is *absent* from the list, a default is used. So we should make
    # sure the expected hashes are *present*.
    # Ensure that all hashes in RUST_SHA256S match the active date.
    for key in RUST_SHA256S.keys():
        if not key.startswith(RUST_NIGHTLY_DATE):
            fail("Inconsistent RUST_SHA256S: Key '{}' does not match RUST_NIGHTLY_DATE '{}'. ".format(key, RUST_NIGHTLY_DATE))

    # Enforce completeness for required platforms.
    # Note: Target-only platforms only require rust-std.
    for triple in SUPPORTED_HOST_TRIPLES:
        for component in SUPPORTED_RUST_COMPONENTS:
            key = "{}/{}-nightly-{}.tar.xz".format(RUST_NIGHTLY_DATE, component, triple)
            if key not in RUST_SHA256S:
                fail("Missing required Rust toolchain hash: '{}'.".format(key))
    for triple in SUPPORTED_TARGET_TRIPLES:
        key = "{}/rust-std-nightly-{}.tar.xz".format(RUST_NIGHTLY_DATE, triple)
        if key not in RUST_SHA256S:
            fail("Missing required Rust std hash: '{}'.".format(key))

def _rust_toolchains_impl(_ctx):
    """Configure all Rust toolchains for the Oak project.

    This extension creates:
    1. Standard toolchains for Linux and macOS (oak_rust_linux, oak_rust_darwin)
    2. Custom toolchains with AVX flags for bare-metal targets (rust_toolchain_repo, etc.)
    3. No-AVX toolchains for stage0 (rust_noavx_toolchain_repo, etc.)
    4. Stdlibs for rebuilding the standard library
    """

    # Validate that all required hashes are present
    _ensure_hashes()

    # Standard Linux toolchain (replaces rust.toolchain() from rules_rust)
    rust_repository_set(
        name = "oak_rust_linux",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_target_triples = {
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
            ],
            "wasm32-unknown-unknown": [
                "@platforms//cpu:wasm32",
                "@platforms//os:none",
            ],
            "wasm32-wasip2": [
                "@platforms//cpu:wasm32",
                "@platforms//os:wasi",
                "@rules_rust//rust/platform:wasi_preview_2",
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # Standard macOS ARM64 toolchain (replaces rust.toolchain() from rules_rust)
    rust_repository_set(
        name = "oak_rust_darwin",
        edition = RUST_EDITION,
        exec_triple = "aarch64-apple-darwin",
        extra_target_triples = {
            "aarch64-apple-darwin": [
                "@platforms//cpu:aarch64",
                "@platforms//os:osx",
            ],
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
            ],
            "wasm32-unknown-unknown": [
                "@platforms//cpu:wasm32",
                "@platforms//os:none",
            ],
            "wasm32-wasip2": [
                "@platforms//cpu:wasm32",
                "@platforms//os:wasi",
                "@rules_rust//rust/platform:wasi_preview_2",
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # Custom Linux toolchain with AVX flags for bare-metal targets
    rust_repository_set(
        name = "rust_toolchain_repo",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_rustc_flags = {
            "x86_64-unknown-none": [
                "--codegen=linker-flavor=gcc",
                "--codegen=relocation-model=static",
                "--codegen=target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
                "--codegen=target-cpu=x86-64-v3",
                "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
            ],
        },
        extra_target_triples = {
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
                str(Label("//bazel/rust:avx_ON")),
                str(Label("//bazel/rust:code_model_NORMAL")),
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # macOS ARM64 toolchain with AVX flags
    rust_repository_set(
        name = "rust_toolchain_repo_darwin_aarch64",
        edition = RUST_EDITION,
        exec_triple = "aarch64-apple-darwin",
        extra_rustc_flags = {
            "x86_64-unknown-none": [
                "--codegen=relocation-model=static",
                "--codegen=target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
                "--codegen=target-cpu=x86-64-v3",
            ],
        },
        extra_target_triples = {
            "aarch64-apple-darwin": [
                "@platforms//cpu:aarch64",
                "@platforms//os:osx",
            ],
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
                str(Label("//bazel/rust:avx_ON")),
                str(Label("//bazel/rust:code_model_NORMAL")),
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # No-AVX Linux toolchain for stage0
    rust_repository_set(
        name = "rust_noavx_toolchain_repo",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_rustc_flags = {
            # Disabling AVX implies soft-float is needed.
            "x86_64-unknown-none": [
                "--codegen=linker-flavor=gcc",
                "--codegen=target-feature=+soft-float",
            ],
        },
        extra_target_triples = {
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
                str(Label("//bazel/rust:avx_OFF")),
                str(Label("//bazel/rust:code_model_NORMAL")),
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # macOS ARM64 no-AVX toolchain
    rust_repository_set(
        name = "rust_noavx_toolchain_repo_darwin_aarch64",
        edition = RUST_EDITION,
        exec_triple = "aarch64-apple-darwin",
        extra_rustc_flags = {
            # Disabling AVX implies soft-float is needed.
            "x86_64-unknown-none": [
                "--codegen=target-feature=+soft-float",
            ],
        },
        extra_target_triples = {
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
                str(Label("//bazel/rust:avx_OFF")),
                str(Label("//bazel/rust:code_model_NORMAL")),
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
        register_toolchain = False,
    )

    # Download rust std library sources
    stdlibs(
        name = "stdlibs",
        build_file = "//bazel/rust:stdlibs.BUILD",
        nightly_date = RUST_NIGHTLY_DATE,
        sha256 = STDLIBS_SHA256,
    )

rust_toolchains = module_extension(
    implementation = _rust_toolchains_impl,
)

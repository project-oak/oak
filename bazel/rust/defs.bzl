"""Functions to set up the various rust-related dependencies."""

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

# This should be kept in sync with the value in flake.nix
# Chosen to match the current internal Rust nightly (go/current-rust-nightly)
# You'll likely need to update the sha256 hashes below as well.
RUST_NIGHTLY_DATE = "2025-03-01"

RUST_NIGHTLY_VERSION = "nightly/" + RUST_NIGHTLY_DATE

RUST_VERSIONS = [
    RUST_NIGHTLY_VERSION,
]

SUPPORTED_HOST_TRIPLES = [
    "x86_64-unknown-linux-gnu",
    "aarch64-apple-darwin",
]

SUPPORTED_TARGET_TRIPLES = [
    "x86_64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-unknown-none",
    "wasm32-unknown-unknown",
]

SUPPORTED_RUST_COMPONENTS = [
    "cargo",
    "clippy",
    "llvm-tools",
    "rust-std",
    "rustc",
    "rustfmt",
]

# Note: be careful here: if a key is *absent* from this map, rules_rust just
# assumes you don't want to verify that component, and will raise a warning but
# will not fail the build. So when updating verions.
# We have some backup checks to try to help make sure all keys are present.
RUST_SHA256S = {
    # Linux x86_64 Host
    "2025-03-01/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "9dfde3b932a240ed7adbef95f9d1437681137c6e0b71ad95b2579cada0623e26",
    "2025-03-01/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "f5cb5053fee14e60bac386caf37a3542f6ac34fd73076e9329e4aac2e6caf640",
    "2025-03-01/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "22ed657fa3092f172cda7ff2c68d560f03e312d0b0d643356d89f4254e858c92",
    "2025-03-01/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "bbfecef0f783ff9fde8485c3739ca71f549e44d9633e58ed5086cf7a09da3fd9",
    "2025-03-01/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "089b01d390bf42e40b2f1eb960033bba83b54c5b70c2d457e0a31ecb99e87f11",
    "2025-03-01/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz": "4f6b4fdcf919e8358b4001d220e2a62208765308dcc8504051c2d3c03efe7fce",
    # macOS ARM64 Host
    "2025-03-01/cargo-nightly-aarch64-apple-darwin.tar.xz": "a69239a4bd94c6b722a8236a24ee06a61da33ffca72fcb06eb75a64435a0952c",
    "2025-03-01/clippy-nightly-aarch64-apple-darwin.tar.xz": "bb1a3f7683520e93ec083359cde495057a207ff231624d0d7ef802ecb5c18c07",
    "2025-03-01/llvm-tools-nightly-aarch64-apple-darwin.tar.xz": "573fc4aa45b92b00a69f5b5ba80cc1b68b4c78ec2dad5af1311607ba34b3f5cb",
    "2025-03-01/rust-std-nightly-aarch64-apple-darwin.tar.xz": "a18eee3a5df3966f11f719f6acadb7a7cc6e8cba590466ec418c7715e605cd52",
    "2025-03-01/rustc-nightly-aarch64-apple-darwin.tar.xz": "a0b4dcdb53e8aa7604ce25a673e3429e7b66a6238f8cc798bf00d37d127e02c3",
    "2025-03-01/rustfmt-nightly-aarch64-apple-darwin.tar.xz": "03569e9884f02a97fee511868f89573562f7c2742b7afd1acfba99fea0b5ffd0",
    # Target-only triples
    "2025-03-01/rust-std-nightly-wasm32-unknown-unknown.tar.xz": "8ca5b9a0de5a3d72b8866638e0255adfdcd5445a1a650a895c3814d41b956c09",
    "2025-03-01/rust-std-nightly-x86_64-unknown-none.tar.xz": "77ee6bffcfd1383903eb5ea095a2a06ae58b8c30312deda75b562402f56dadb0",
}

STDLIBS_SHA256 = "4743b974292186c91f4daba45de20edfbc6aa293671953aca30168608e69609e"

# If updates change stdlib dependencies, you may need to update these. Hunt
# around in your bazel cache's `$BAZEL_CACHE/external/stdlibs/vendor` path to see what's available.
# Most likely you can just pick the latest one.
STDLIBS_DEPS_VERSIONS = {
    "compiler_builtins": "0.1.148",
    "cfg-if": "1.0.0",
    "libc": "0.2.169",
    "rustc-demangle": "0.1.24",
}

RUST_EDITION = "2024"

def _ensure_hashes():
    # If a hash is *absent* from the list, a default is used. So we should make
    # sure the expect hashes are *present*.
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

def setup_rust_dependencies(oak_repo_name = "oak"):
    """Set up the various rust-related dependencies. Call this after load_rust_repositories().


    Args:
        oak_repo_name: to be used when Oak repo is renamed.
    """
    _ensure_hashes()

    rules_rust_dependencies()

    rust_register_toolchains(
        edition = RUST_EDITION,
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
    )

    # Creates remote repositories for Rust toolchains, required for cross-compiling.
    # Linux toolchain
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
                "@%s//bazel/rust:avx_ON" % oak_repo_name,
                "@%s//bazel/rust:code_model_NORMAL" % oak_repo_name,
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
    )

    # macOS ARM64 toolchain
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
                "@%s//bazel/rust:avx_ON" % oak_repo_name,
                "@%s//bazel/rust:code_model_NORMAL" % oak_repo_name,
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
    )

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
                "@%s//bazel/rust:avx_OFF" % oak_repo_name,
                "@%s//bazel/rust:code_model_NORMAL" % oak_repo_name,
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
    )

    # macOS ARM64 noavx toolchain
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
                "@%s//bazel/rust:avx_OFF" % oak_repo_name,
                "@%s//bazel/rust:code_model_NORMAL" % oak_repo_name,
            ],
        },
        versions = RUST_VERSIONS,
        sha256s = RUST_SHA256S,
    )

    # IDE support via rust-analyzer for bazel-only projects.
    # https://bazelbuild.github.io/rules_rust/rust_analyzer.html
    #
    # You can re-generate the rust-project.json file using:
    # bazel run @rules_rust//tools/rust_analyzer:gen_rust_project
    #
    # It should not be committed.
    #
    # VSCode users: There's a task included in .vscode/tasks.json that should
    # automatically do this for you when needed.
    rust_analyzer_dependencies()

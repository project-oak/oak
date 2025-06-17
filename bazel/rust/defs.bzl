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

# To get the latest SHA256, use the get_sha256s.sh helper script.
RUST_SHA256S = {
    # Linux x86_64
    "2025-04-03/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "adfe5bd8fb807bfd8fee2ede9d88853837ba9dcf14dd701edeb33a8c9d84a6f2",
    "2025-04-03/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "06839db5cd1810032a3115211b558b257c75f8459645265e310f0c518c9ad2d8",
    "2025-04-03/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "e2adf4c25541e7abf7e0c4e6586c94ac662fb9ae3e78b1f7310789bfc1cb5860",
    "2025-04-03/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "6b3b7dc16ccb0204bcc2fc381ffe69d1eaddf326583c11d24699797ebd0778c6",
    "2025-04-03/rust-std-nightly-wasm32-unknown-unknown.tar.xz": "e9e98ec5cb439842c2eaa14abeaacbb22e0da169dadb18f1f6de7ffadb3b4829",
    "2025-04-03/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "2418663236236373c3d278e6e602ef5ad3158b9cebd5c1095f7916dbd9c9b891",
    "2025-04-03/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz": "f8876b429b1ad9dfd5ece1e47947b39b20a0ecc56b1c76a614c4af5797152d86",
    # macOS ARM64
    "2025-04-03/cargo-nightly-aarch64-apple-darwin.tar.xz": "482f5759a9e985fefe139f9a64a18dd28f99719f14207b403b447e6fa19d2d7b",
    "2025-04-03/clippy-nightly-aarch64-apple-darwin.tar.xz": "d8a46adc0171899706a0cc98d60a57369dbc4b109d3f052e2bc043028d77d682",
    "2025-04-03/llvm-tools-nightly-aarch64-apple-darwin.tar.xz": "68017935fc80042ed5b47cafe4d92bb006d5a4652b8da02d09adaa531a1694e2",
    "2025-04-03/rust-std-nightly-aarch64-apple-darwin.tar.xz": "004a7fee96f35e258fa7fcbf66b06c6a53426365715fc02cfcba3ed0a8d1832c",
    "2025-04-03/rustc-nightly-aarch64-apple-darwin.tar.xz": "6538a7232af263e84a4aac73d6858b6e9b44478bd48f16b1c53c027ab0278ad1",
    "2025-04-03/rustfmt-nightly-aarch64-apple-darwin.tar.xz": "52e7e729422369382a32a29ab3b208dfe79027d83416e136c100ab31bed74caf",
}

# To get the latest SHA256, use the get_sha256s.sh helper script.
# curl https://static.rust-lang.org/dist/$RUST_NIGHTLY_VERSION/rustc-nightly-src.tar.gz.sha256
STDLIBS_SHA256 = ""

# If updates change stdlib dependencies, you may need to update these. Hunt
# around in your bazel cache's `$BAZEL_CACHE/external/stdlibs/vendor` path to see what's available.
# Most likely you can just pick the latest one.
STDLIBS_DEPS_VERSIONS = {
    "compiler_builtins": "0.1.148",
    "cfg-if": "1.0.0",
    "libc": "0.2.169",
    "rustc-demangle": "0.1.24",
}

RUST_EDITION = "2021"

def setup_rust_dependencies(oak_repo_name = "oak"):
    """Set up the various rust-related dependencies. Call this after load_rust_repositories().


    Args:
        oak_repo_name: to be used when Oak repo is renamed.
    """
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
                "-Clinker-flavor=gcc",
                "-Crelocation-model=static",
                "-Ctarget-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
                "-Ctarget-cpu=x86-64-v3",
                "-Clink-arg=-Wl,-zmax-page-size=0x200000",
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
        extra_target_triples = {
            "aarch64-apple-darwin": [
                "@platforms//cpu:aarch64",
                "@platforms//os:osx",
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
                "-Clinker-flavor=gcc",
                "-C",
                "target-feature=+soft-float",
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

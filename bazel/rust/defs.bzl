"""Functions to set up the various rust-related dependencies."""

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

# This should be kept in sync with the value in flake.nix
# Chosen to match the current internal Rust nightly (go/current-rust-nightly)
RUST_NIGHTLY_DATE = "2024-09-05"

RUST_NIGHTLY_VERSION = "nightly/" + RUST_NIGHTLY_DATE

RUST_VERSIONS = [
    RUST_NIGHTLY_VERSION,
]

# Note: I was tempted to use the RUST_NIGHTLY_DATE symbol here, but this
# dictionary literal gets printed out when you build, so it's easier to just
# paste it as-is.
RUST_SHA256S = {
    "2024-09-05/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "cca47094fbd0b5e677adc8f68f4b7b5b74b13028d9ed05244049de3896ef4be2",
    "2024-09-05/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "d16362b2cdcad8f90e40598bcb39c303f979cb6981ad7f334b630917ad4b2596",
    "2024-09-05/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "bfb8064dec80ba5988620e23fbb5730753f35662a70e6d52e7c80a675ec05e3b",
    "2024-09-05/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "cd045f86c0d4e3b3647000096d46aabcb55c408915578f593dfa65a3d8453c10",
    "2024-09-05/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "1be4c36649cd2ec214e8c43ca63fb38d09dd2d5a76eefc8e33cee8025286a09d",
    "2024-09-05/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz": "c4433dae8219c9e619adaeaa903f27c233cd1a84a75a1b7112445bbe3e12a35c",
    "2024-09-05/rust-std-nightly-wasm32-unknown-unknown.tar.xz": "0295fce4801daef5a569dfb38b403f5b1d185b64c0bace4c9869b9631957dcec",
}

STDLIBS_SHA256 = "894cfc1fb6316acef5c4095aab8713f56bd57f90db5dfb75788b8ab995f86657"

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
    rust_repository_set(
        name = "rust_toolchain_repo",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_rustc_flags = {
            "x86_64-unknown-none": [
                "-Crelocation-model=static",
                "-Ctarget-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
                "-Ctarget-cpu=x86-64-v3",
                "-Clink-arg=-zmax-page-size=0x200000",
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

    rust_repository_set(
        name = "rust_noavx_toolchain_repo",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_rustc_flags = {
            # Disabling AVX implies soft-float is needed.
            "x86_64-unknown-none": ["-C", "target-feature=+soft-float"],
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

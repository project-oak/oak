"""Functions to set up the various rust-related dependencies."""

# This should be kept in sync with the value in flake.nix
# Chosen to match the current internal Rust nightly (go/current-rust-nightly)
# You'll likely need to update the sha256 hashes below as well.
RUST_NIGHTLY_DATE = "2026-04-11"

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
    "wasm32-wasip2",
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
    "2026-04-11/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "b4c95336c94a70b33f5b7b471315c8b4ab0a10c5c936554d73101d8e9dd76444",
    "2026-04-11/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "658854d7dd8c4ed312ed703768578fed74509775a6053f3552663f4074c8c03f",
    "2026-04-11/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "133a0d5c074964af93661ba86d1200b4363c16ab1cbcdb57d56818610a6d2ad7",
    "2026-04-11/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "e438f81cb8340e1093d7e799c6e742eb76779b360146d178b7104b4f7a89b3e1",
    "2026-04-11/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "6c32f2c2bf33b2d45a5f969f5d30c764f3c5c35179af65f7dae3448779bdfa89",
    "2026-04-11/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz": "f64247b36ca1de77472e194027c1d28a0b8fe1fa27c7fd25dd0f8715ef051f7a",
    # macOS ARM64 Host
    "2026-04-11/cargo-nightly-aarch64-apple-darwin.tar.xz": "b52f3de5fbbfc96912798f7d41917cd8bb6e7d37b1445e8aab84aee55a64e6c0",
    "2026-04-11/clippy-nightly-aarch64-apple-darwin.tar.xz": "556b6626673ad8264f0d9c3a4e94af7a1be0e151907a759c03b566e53bb08394",
    "2026-04-11/llvm-tools-nightly-aarch64-apple-darwin.tar.xz": "9c0af22e6ce87c8ff8e27ce72d398a890197123cdd1f23eda144f88badb3ed15",
    "2026-04-11/rust-std-nightly-aarch64-apple-darwin.tar.xz": "03b79ff37e48d7ef916ce453fc4f2d0f7e150552b9e02cd1b28377f3a4af1bed",
    "2026-04-11/rustc-nightly-aarch64-apple-darwin.tar.xz": "07c67d50eab56d5e63329967bd25387beb5a53824583fdbe910ad1b41868499f",
    "2026-04-11/rustfmt-nightly-aarch64-apple-darwin.tar.xz": "7a637a2a8757275cfec71c47d41d3f02480fefe31e029e17cf77c25162212afa",
    # Target-only triples
    "2026-04-11/rust-std-nightly-wasm32-unknown-unknown.tar.xz": "72206748af37a2c9938fd9bb27d56b32dc6d92c3ad443dda5ee99351a4d59a94",
    "2026-04-11/rust-std-nightly-wasm32-wasip2.tar.xz": "31f33c2374620a7365f40d46528997cd43c80cc14a14662ef316febefb0305b3",
    "2026-04-11/rust-std-nightly-x86_64-unknown-none.tar.xz": "0b484e14e6a82f74062928210f7cba53470487265e52c6621b70dee0a024c3e2",
}

STDLIBS_SHA256 = "7a45b8e66cc4a451684ce551bc43d17c3915a74bffd1dd1f01f17ffff8b5349a"

# If updates change stdlib dependencies, you may need to update these. Hunt
# around in your bazel cache's `$BAZEL_CACHE/external/stdlibs/vendor` path to see what's available.
# Most likely you can just pick the latest one.
STDLIBS_DEPS_VERSIONS = {
    "cfg-if": "1.0.4",
    "libc": "0.2.184",
    "rustc-demangle": "0.1.27",
}

RUST_EDITION = "2024"

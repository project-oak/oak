"""Functions to set up the various rust-related dependencies."""

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
    "2025-03-01/rust-std-nightly-wasm32-wasip2.tar.xz": "83d6c2b3c4ad1257c5ce2ff0c0821011d83ef2a31157e5ff76f2544c89877af5",
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

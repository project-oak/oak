#!/bin/bash
RUST_NIGHTLY_VERSION=2025-04-03

echo "=== Linux x86_64 ==="
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rust-std-nightly-wasm32-unknown-unknown.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz.sha256"

echo "=== macOS ARM64 ==="
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/clippy-nightly-aarch64-apple-darwin.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/cargo-nightly-aarch64-apple-darwin.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/llvm-tools-nightly-aarch64-apple-darwin.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rustc-nightly-aarch64-apple-darwin.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rust-std-nightly-aarch64-apple-darwin.tar.xz.sha256"
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rustfmt-nightly-aarch64-apple-darwin.tar.xz.sha256"

echo "=== Source ==="
curl "https://static.rust-lang.org/dist/${RUST_NIGHTLY_VERSION}/rustc-nightly-src.tar.gz.sha256"

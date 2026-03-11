# Oak Rust Toolchain Configuration

This directory contains the Rust toolchain configuration for the Oak project,
managed via Bazel's bzlmod system.

## Overview

Oak uses multiple Rust toolchains to support different build targets:

| Toolchain Type | Purpose                         | Target Triples                                                               |
| -------------- | ------------------------------- | ---------------------------------------------------------------------------- |
| Standard       | Regular Rust code               | `x86_64-unknown-linux-gnu`, `wasm32-unknown-unknown`, `aarch64-apple-darwin` |
| Custom AVX     | Restricted kernel (with AVX)    | `x86_64-unknown-none`                                                        |
| Custom No-AVX  | Restricted kernel (without AVX) | `x86_64-unknown-none`                                                        |
| Rebuilt Stdlib | Stage0 firmware                 | `x86_64-unknown-none`                                                        |

## Toolchain Categories

### 1. Standard Toolchains (`oak_rust_linux`, `oak_rust_darwin`)

For most Rust code: Linux binaries, WebAssembly modules, and macOS development.
Uses pre-built standard libraries from the Rust distribution.

### 2. Custom AVX Toolchains (`rust_toolchain_repo`, `rust_noavx_toolchain_repo`)

For bare-metal targets (`x86_64-unknown-none`):

- **AVX variant**: Enables AVX/AVX2/SSE instructions for performance-critical
  code in the restricted kernel.
- **No-AVX variant**: Uses soft-float for early boot code that runs before AVX
  is available.

These use constraint values `//bazel/rust:avx_ON` or `//bazel/rust:avx_OFF` for
toolchain selection.

### 3. Rebuilt Stdlib Toolchains (`toolchain_rebuilt_x86_64-unknown-none`)

**Only used by stage0 firmware** (`//:x86_64-firmware` platform).

Rebuilds the Rust standard library from source with special flags:

- `--codegen=code-model=large`: Required because firmware ROM is at ~4GiB while
  execution memory is below 1MiB (offset exceeds 2GiB).
- `--codegen=opt-level=z`: Size optimization for firmware.
- `--cfg=aes_force_soft`, `--cfg=polyval_force_soft`: Software crypto
  implementations.

Selected via constraints: `avx_OFF` + `code_model_LARGE`.

## Key Files

| File                                                 | Purpose                                           |
| ---------------------------------------------------- | ------------------------------------------------- |
| [`defs.bzl`](defs.bzl)                               | Rust version, SHA256 hashes, and shared constants |
| [`extensions.bzl`](extensions.bzl)                   | Bzlmod extension that creates all toolchains      |
| [`stdlibs.bzl`](stdlibs.bzl)                         | Repository rule for downloading stdlib sources    |
| [`rebuilt_toolchain/BUILD`](rebuilt_toolchain/BUILD) | Rebuilt stdlib toolchain definitions              |

## Updating the Rust Version

1. Update `RUST_NIGHTLY_DATE` in [`defs.bzl`](defs.bzl)
2. Update all SHA256 hashes in `RUST_SHA256S` (the extension will fail with
   helpful error messages if any are missing)
3. Update `STDLIBS_SHA256` for the stdlib sources
4. Run a build to verify

## Usage in Subprojects

Subprojects (`codelab/`, `oak_private_memory/`) use Oak's Rust toolchain to
ensure version consistency. This avoids potential issues from mismatched Rust
versions when depending on Oak crates.

```starlark
oak_rust = use_extension("@oak//bazel/rust:extensions.bzl", "rust_toolchains")
use_repo(oak_rust, "oak_rust_linux__x86_64-unknown-linux-gnu__nightly")
register_toolchains("@oak_rust_linux__x86_64-unknown-linux-gnu__nightly//:all")
```

# BoringSSL for Oak Restricted Kernel

This directory contains the build integration and Rust FFI bindings for
[BoringSSL](https://boringssl.googlesource.com/boringssl/) on the Oak Restricted
Kernel `x86_64-unknown-none` target.

## Architecture

BoringSSL is fetched as a Bazel module dependency (`@boringssl`) with
`archive_override` in `MODULE.bazel` to apply Oak-specific patches.  The patches
live under `patches/` and are applied automatically during module resolution.

### Patches

| Patch | Purpose |
|-------|---------| 
| `01_oak_platform.patch` | Add `OPENSSL_OAK` platform define to `target.h` |
| `02a_oak_rand_internal.patch` | Add `OPENSSL_RAND_OAK` to `crypto/rand/internal.h` |
| `02b_oak_rand_sources.patch` | Add `crypto/rand/oak.cc` to `gen/sources.bzl` |
| `03b_oak_build_bazel.patch` | Add `os:none` copts/deps to `BUILD.bazel` |
| `04_rust_module.patch` | Add `rules_rust` / `rules_rust_bindgen` Bazel deps to `MODULE.bazel` |
| `05_rust_no_std.patch` | Prepend `#![no_std]` to `rust/bssl-macros/src/lib.rs` |
| `06_rust_wrapper.patch` | Strip SSL header includes from `rust/bssl-sys/wrapper.h` |
| `07_oak_rand_source.patch` | Create `crypto/rand/oak.cc` (`CRYPTO_sysrand` via `RDRAND`) |
| `08_rust_build.patch` | Create `rust/BUILD.bazel` (Bazel targets for the Rust crates) |

New files (`crypto/rand/oak.cc`, `rust/BUILD.bazel`) are created with
git-format patches (`new file mode`, patches `07`/`08`), which Bazel's native
patcher applies just like ordinary unified diffs. Patches are kept as
single-file diffs because the patcher mispositions hunks when several files
share one patch.

Patches `04`–`08` add Bazel Rust support (the `rust/BUILD.bazel` targets and
their module dependencies) and are structured to be upstreamable to BoringSSL
— they carry no Oak-specific dependencies.

The C library functions BoringSSL needs are provided directly by the LLVM libc
port (`//third_party/llvm_libc:llvm_libc`).

### Rust bindings

The Rust bindings use the **upstream BoringSSL Rust crate sources** directly,
built via Bazel targets in `@boringssl//rust` (`rust/BUILD.bazel`):

| Target | Upstream crate | Purpose |
|--------|---------------|---------| 
| `//rust:bssl_sys_bindgen` | — | `rust_bindgen` rule generating FFI bindings from `wrapper.h` |
| `//rust:bssl_macros` | [`rust/bssl-macros`](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-macros/) | `bssl_enum!` macro used by `bssl_sys` |
| `//rust:bssl_sys` | [`rust/bssl-sys`](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-sys/) | Raw FFI bindings (`#![no_std]`) |
| `//rust:bssl_crypto` | [`rust/bssl-crypto`](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-crypto/) | Safe, idiomatic Rust wrappers (`no_std` with `alloc`) |

The `rust_bindgen` flags match the upstream CMake build
([`rust/bssl-sys/CMakeLists.txt`](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-sys/CMakeLists.txt))
to ensure full compatibility with the `bssl-crypto` crate:

- `--default-macro-constant-type=signed` — constants like `EVP_PKEY_RSA` are
  emitted as `i32`, matching the types expected by `bssl-crypto`
- `--rustified-enum=point_conversion_form_t` — generates a Rust enum required
  by the `ec` module
- `wrap_static_fns = True` — generates C wrappers for static inline functions
  like `CBS_init` / `CBS_len`

The upstream `bssl-sys/src/lib.rs` supports Bazel natively via a `bindgen_rs_file`
cfg flag: when set, it includes the generated bindings from the path in the
`BINDGEN_RS_FILE` environment variable instead of using Cargo's `OUT_DIR`.

Usage from a `no_std` enclave app:

```rust
use bssl_crypto::aead::{Aead, Aes256Gcm};

let key: &[u8; 32] = /* ... */;
let nonce: &[u8; 12] = /* ... */;
let aead = Aes256Gcm::new(key);
let ciphertext = aead.seal(nonce, plaintext, aad);
let plaintext = aead.open(nonce, &ciphertext, aad);
```

### Oak-specific BUILD target

The local [`BUILD`](BUILD) file in this directory defines only
`:boringssl_crypto` — a thin `cc_library` that re-exports `@boringssl//:crypto`
with the LLVM libc and libc++ dependencies needed on the `os:none` platform.
All Rust crate targets live in the BoringSSL external repo at
`@boringssl//rust:*`.

## Platform design

Oak is registered as a new platform in `include/openssl/target.h`.  It disables:

- **Filesystem** (`OPENSSL_NO_FILESYSTEM`) — no persistent storage
- **POSIX I/O** (`OPENSSL_NO_POSIX_IO`) — no file descriptors beyond RK
  channels
- **Sockets** (`OPENSSL_NO_SOCK`) — no networking
- **Threads** (`OPENSSL_NO_THREADS_CORRUPT_MEMORY_AND_LEAK_SECRETS_IF_THREADED`)
  — single-threaded enclave

Random number generation uses x86 `RDRAND` via a custom `CRYPTO_sysrand`
implementation in `crypto/rand/oak.cc`.  In a TEE context (AMD SEV-SNP / Intel
TDX), RDRAND output is not under host control.

Assembly optimizations are **enabled** — the pre-generated Linux x86_64 assembly
files (AES-NI, AVX2, AVX-512, GHASH, SHA, RDRAND, etc.) use the SysV x86_64
calling convention which is compatible with Oak Restricted Kernel.

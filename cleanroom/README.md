# Cleanroom

**A heavily sandboxed WebAssembly runner for LLM agents.**

Cleanroom lets you safely execute arbitrary, untrusted WebAssembly (Wasm)
modules. The module has **no access** to the local filesystem, the network, or
environment variables — the only I/O channel is bytes piped through the
cleanroom binary.

This makes it safe for LLM agents to run user-supplied or agent-generated code
without risking leaking host data or causing side-effects. Because modules are
standard `.wasm` binaries, they are fully **portable across platforms** (macOS,
Linux, etc.).

## Design

Cleanroom reuses the battle-tested **Oak Functions ABI** — the same runtime
stack used by Oak Functions and Oak Verity for confidential serverless
workloads. This gives us:

- **[`oak_functions_service`]** on the host: `OakFunctionsInstance<WasmHandler>`
  drives a `wasmtime` JIT with fuel limits, memory limits, and a sandboxed
  linker. All host imports are controlled through the Oak Functions ABI; the
  cleanroom runner exposes only the minimal set needed for request/response I/O.
- **[`oak_functions_sdk`]** (via `cleanroom_sdk`) on the guest: provides
  `read_request` / `write_response`, the `alloc` export, and the `run_with`
  convenience helper.

## Security model

| Property              | Guarantee                                                         |
| --------------------- | ----------------------------------------------------------------- |
| Filesystem access     | ❌ None — no WASI, host imports limited to ABI                    |
| Network access        | ❌ None                                                           |
| Environment variables | ❌ None                                                           |
| Syscalls              | ❌ None — pure Wasm interpreter (wasmtime/Cranelift JIT)          |
| I/O                   | ✅ Stdin → Wasm → Stdout only                                     |
| Fuel / CPU budget     | ✅ Enforced by `wasmtime` (configurable; prevents infinite loops) |
| Memory budget         | ✅ Enforced by `wasmtime` linear memory limits                    |
| Portability           | ✅ `.wasm` modules are platform-independent                       |

## Building

```bash
# Build the runner binary
bazel build //cleanroom:cleanroom

# Build all examples
bazel build //cleanroom/examples/...

# Run all integration tests
bazel test //cleanroom:cleanroom_integration_test
```

## Usage

```bash
# Create an alias for the runner (stable regardless of which platform Bazel last configured):
alias cleanroom="$(bazel cquery --output=files //cleanroom:cleanroom)"

echo "hello world" | cleanroom --wasm-module-file="$(bazel cquery --output=files //cleanroom/examples/to_uppercase:to_uppercase_wasm)"
# → HELLO WORLD

echo -n "hello" | cleanroom --wasm-module-file="$(bazel cquery --output=files //cleanroom/examples/reverse:reverse_wasm)"
# → olleh

printf "foo\nbar baz\n" | cleanroom --wasm-module-file="$(bazel cquery --output=files //cleanroom/examples/word_count:word_count_wasm)"
# → 2 3 12
```

## Examples

| Module         | Source                                             | Description                         |
| -------------- | -------------------------------------------------- | ----------------------------------- |
| `to_uppercase` | [`examples/to_uppercase/`](examples/to_uppercase/) | ASCII uppercase                     |
| `reverse`      | [`examples/reverse/`](examples/reverse/)           | Reverse bytes                       |
| `word_count`   | [`examples/word_count/`](examples/word_count/)     | Count lines/words/bytes (like `wc`) |

## Writing your own module

Add a `rust_shared_library` in Bazel with
`platform = "//:wasm32-unknown-unknown"` and depend on
`//cleanroom/sdk:cleanroom_sdk`. Call [`cleanroom_sdk::run_with`] from your
exported `main` function:

```rust
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    cleanroom_sdk::run_with(|input: &[u8]| -> Vec<u8> {
        // Transform input bytes → output bytes.
        input.iter().map(|b| b.to_ascii_uppercase()).collect()
    });
}
```

### BUILD file

```python
load("@rules_rust//rust:defs.bzl", "rust_shared_library")

rust_shared_library(
    name = "my_module_wasm",
    srcs = ["wasm.rs"],
    crate_name = "my_module",
    platform = "//:wasm32-unknown-unknown",
    deps = ["//cleanroom/sdk:cleanroom_sdk"],
)
```

## ABI reference

The module must export:

| Export   | Signature          | Provided by         |
| -------- | ------------------ | ------------------- |
| `memory` | (memory)           | Rust runtime        |
| `alloc`  | `(u32) -> *mut u8` | `oak_functions_sdk` |
| `main`   | `() -> ()`         | Module author       |

Inside `main`, use `oak_functions_sdk::read_request()` to receive the stdin
bytes and `oak_functions_sdk::write_response()` to send back the output bytes.
`cleanroom_sdk::run_with` wraps both calls for you.

## Project structure

```text
cleanroom/
  BUILD                   — Bazel: runner binary + integration tests
  README.md               — This file
  src/
    main.rs               — Cleanroom runner (uses OakFunctionsInstance)
  sdk/
    lib.rs                — Guest SDK wrapping oak_functions_sdk
    BUILD
  examples/
    to_uppercase/         — ASCII uppercase
    reverse/              — Reverse bytes
    word_count/           — Line/word/byte counter (like wc)
  tests/
    integration_test.rs   — End-to-end Bazel tests
```

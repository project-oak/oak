# LLVM libc for Oak Restricted Kernel

This directory contains the build configuration for
[LLVM libc](https://libc.llvm.org/) (version 22.1.0), configured as a
full-build port targeting Oak Restricted Kernel on x86\_64.

The upstream source is fetched at build time via `http_archive` (see
`MODULE.bazel`); only the Oak-specific additions, the CMake patch, and the
Bazel glue live in this directory.

The Oak port relies heavily on the existing `baremetal` target.

The build selects the Oak port through the target triple
`x86_64-unknown-oak-elf` (passed as `LIBC_TARGET_TRIPLE` in
[`BUILD`](BUILD)). CMake derives `LIBC_TARGET_OS = "oak"` from the triple,
which in turn selects `libc/config/oak/` and the `libc/src/.../oak/`
implementations.

### Oak-specific components

| Component | Path (inside the source tree) | Purpose |
|-----------|-------------------------------|---------|
| Config | `libc/config/oak/` | Entrypoints, headers, and feature knobs |
| OSUtil | `libc/src/__support/OSUtil/oak/` | `exit()` and `write_to_stderr()` |
| stdlib | `libc/src/stdlib/oak/` | `malloc`/`free`/`calloc`/`realloc`/`aligned_alloc` (Oak-specific, Rust heap); `abort` (re-exports baremetal) |
| stdio | `libc/src/stdio/oak/` | `printf`, `puts`, `putchar`, `getchar`, `vprintf`, `remove` (all re-export baremetal) |

## Vendor callbacks

The Oak port expects a small number of symbols to be provided by the enclave
runtime. These are implemented once in
[`oak_enclave_runtime_support`](../../oak_enclave_runtime_support) (module
`llvm_libc`), which every enclave application links transitively via
`oak_restricted_kernel_sdk`, so individual applications do not need to define
them:

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `__llvm_libc_exit` | `extern "C" fn(i32) -> !` | Terminate the enclave |
| `__llvm_libc_malloc` | `extern "C" fn(usize, usize) -> *mut c_void` | Allocate `size` bytes with `alignment` from the shared heap |
| `__llvm_libc_free` | `extern "C" fn(*mut c_void, usize, usize)` | Free a block, given its original `size` and `alignment` |
| `__llvm_libc_stdio_write` | `extern "C" fn(*mut c_void, *const c_char, usize) -> isize` | Write bytes to an output channel |
| `__llvm_libc_stdio_read` | `extern "C" fn(*mut c_void, *mut c_char, usize) -> isize` | Read bytes from an input channel |
| `__llvm_libc_stdin_cookie` | `extern "C" static` | Opaque cookie for stdin |
| `__llvm_libc_stdout_cookie` | `extern "C" static` | Opaque cookie for stdout |
| `__llvm_libc_stderr_cookie` | `extern "C" static` | Opaque cookie for stderr |

The I/O and exit callbacks follow the same convention as the upstream
baremetal port, documented in the LLVM libc source at
`libc/src/__support/OSUtil/baremetal/io.cpp`.

### Heap / allocation

The `malloc` family does **not** use LLVM libc's built-in `freelist`/`scudo`
allocators, nor the baremetal `_end`/`__llvm_libc_heap_limit` linker symbols.
Instead `libc/src/stdlib/oak/` delegates every allocation to the
`__llvm_libc_malloc`/`__llvm_libc_free` callbacks above, which the Rust runtime
implements on top of its global allocator. This gives C and Rust a **single
shared heap** (managed by `oak_enclave_runtime_support`), rather than the C
library owning a separate static region.

Because C `free`/`realloc` receive only a pointer, while Rust's `GlobalAlloc`
(and [`core::alloc::Layout`]) requires the size and alignment on deallocation,
each allocation is prefixed with a small header recording the size and
alignment so they can be replayed on free. See
`libc/src/stdlib/oak/oak_malloc.h` for the bookkeeping and
<https://doc.rust-lang.org/core/alloc/trait.GlobalAlloc.html> for the Rust
contract the callbacks mirror.

[`core::alloc::Layout`]: https://doc.rust-lang.org/core/alloc/struct.Layout.html

## Header generation

LLVM libc generates its public headers with `hdrgen`, a Python tool that
imports the `yaml` module (PyYAML) and calls `yaml.safe_load`. The Python that
`rules_foreign_cc`'s CMake build finds in the Bazel sandbox does not have
PyYAML on its default `sys.path`, so the CMake rule sets `PYTHONPATH` to a
directory that does.

## Updating to a newer LLVM release

1. Update the `llvm_libc_src` `http_archive` in `MODULE.bazel` (URL, integrity,
   strip\_prefix).
2. PyYAML (needed by `hdrgen`) is pinned independently as the `@pyyaml_src`
   `http_archive` and is provided hermetically (see
   [Header generation](#header-generation) above), so an LLVM bump needs no
   change here. Bump `@pyyaml_src` only to update PyYAML itself.
3. Re-apply / refresh `patches/oak_cmake.patch`. It modifies these upstream
   files:
   - `libc/cmake/modules/LLVMLibCArchitectures.cmake` — recognise the `oak`
     target OS (`LIBC_TARGET_OS_IS_OAK`).
   - `libc/CMakeLists.txt` — write the generated config doc into the build
     directory (the source tree is read-only in the Bazel sandbox).
   - `libc/lib/CMakeLists.txt` — exclude `oak` from `libc-startup` install.
   - `libc/src/stdlib/CMakeLists.txt` — exclude `oak` from the scudo path,
     route `oak` through the baremetal-style allocator aliases, and drop the
     `atexit` dependency of `exit` (Oak is single-threaded, so
     `exit_handler`/`atexit` are unavailable).
   - `libc/include/CMakeLists.txt` — add the missing `wchar_t` type header to
     the `stdlib` header target. Upstream 22.1's `stdlib.yaml` lists `wchar_t`
     among its types (so `hdrgen` emits `#include
     "llvm-libc-types/wchar_t.h"`) but the header target's `DEPENDS` omits it,
     which would otherwise leave the referenced header uninstalled.
4. New Oak files live under `overlay/`. The `stdio` entrypoints and `abort`
   are thin re-exports of the upstream baremetal sources (they `#include
   "src/stdio/baremetal/..."` / `"src/stdlib/baremetal/abort.cpp"`), so
   upstream fixes flow through automatically — but verify those baremetal
   paths still exist after a bump. Only the `malloc` family is a genuine Oak
   implementation that needs review.

## Excluded functionality

The following categories of libc functionality are intentionally excluded
because Oak Restricted Kernel has no filesystem or process model:

- **File I/O** (`fopen`, `fclose`, `fread`, `fwrite`, `fprintf`, etc.)
- **Process management** (`fork`, `exec`, `wait`, etc.)
- **Networking** (`socket`, `connect`, `bind`, etc.)
- **atexit handlers** (no process lifecycle)
- **Scudo / freelist allocators** (the `malloc` family delegates to the Rust
  host heap instead — see [Heap / allocation](#heap--allocation))

Functions like `printf` and `puts` are available but route through the
vendor-provided `__llvm_libc_stdio_write` callback, and `malloc`/`free` route
through the vendor-provided allocation callbacks.

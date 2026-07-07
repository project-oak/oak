<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"><img alt="Project Oak Restricted Kernel Logo" src="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

Runtime support library for applications built for Oak Restricted Kernel.

For now, the runtime support library provides:

- a global heap allocator (module `heap`);
- math (`libm`) symbols required by dependencies compiled to C (module `libm`);
- the LLVM libc vendor callbacks (`__llvm_libc_*` for heap, exit, stdio, time
  and errno) required by the Oak port of LLVM libc (module `llvm_libc`). These
  delegate to the shared global allocator and the Restricted Kernel syscalls, so
  any enclave application that links the Oak libc gets a working C runtime
  automatically. See [`third_party/llvm_libc`](../third_party/llvm_libc) for
  details. The same module also supplies the two C++ CRT symbols the compiler
  emits for static-destructor registration (`__dso_handle` and `__cxa_atexit`)
  that libc++abi does not own.

## Testing

[`tests/libc`](tests/libc) holds an end-to-end integration test that boots the
FFI test app (`//oak_enclave_runtime_support/tests/libc/app`) under Oak
Restricted Kernel and checks that the libc-backed C code runs correctly through
the vendor callbacks above.

[`tests/libcxx`](tests/libcxx) is the analogous end-to-end test for the LLVM
libc++ port: it boots a C++ FFI test app that exercises the C++ standard library
(`std::vector`, `std::string`, `std::unique_ptr`, ...), which in turn relies on
the same vendor callbacks.

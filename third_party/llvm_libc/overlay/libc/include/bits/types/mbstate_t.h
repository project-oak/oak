// Minimal mbstate_t definition for Oak Restricted Kernel.
//
// libc++'s <__mbstate_t.h> sources the `mbstate_t` typedef from the C library
// via a fixed cascade of preprocessor branches. LLVM libc does define the type
// in its own <llvm-libc-types/mbstate_t.h>, and newer libc++ revisions include
// that directly through a `#elif _LIBCPP_LIBC_LLVM_LIBC` branch (enabled by the
// CMake option RUNTIMES_USE_LIBC=llvm-libc). The libc++ revision pinned by this
// project (llvmorg-22.1.0) predates that branch, so on the Oak platform (not
// musl, glibc, or Darwin, and with no include_next-reachable
// <wchar.h>/<uchar.h>) the only branch libc++ can take is
// `#elif __has_include(<bits/types/mbstate_t.h>)`. We therefore supply that
// header here.
//
// This file is not a generated LLVM libc public header, so the default install
// step does not ship it. The `llvm_libc` cmake() target's `postfix_script`
// copies it into `$INSTALLDIR/include/bits/types/` so it lands on the same
// include path as the generated Oak libc headers. That single install location
// serves both the libc++ build (which searches the installed libc headers) and
// every downstream libc++ consumer (which picks up the libc headers re-exported
// by `:llvm_libc` through `:llvm_libcxx`), so no separate include directory or
// `cc_library` is needed.
//
// The `_LIBCPP_LIBC_LLVM_LIBC` branch is absent from the entire LLVM 22.x
// release series (verified through llvmorg-22.1.8) and is present on `main`, so
// it should first ship in LLVM 23. Once the pinned LLVM includes it, this shim
// can be dropped in favor of setting RUNTIMES_USE_LIBC=llvm-libc in the
// `llvm_libcxx` cmake() rule.
// See llvm-project/libcxx/include/__mbstate_t.h.

#ifndef OAK_BITS_TYPES_MBSTATE_T_H
#define OAK_BITS_TYPES_MBSTATE_T_H

typedef struct {
  unsigned long __opaque;
} mbstate_t;

#endif

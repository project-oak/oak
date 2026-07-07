//===-- Oak heap delegation to the Rust global allocator ------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIBC_SRC_STDLIB_OAK_OAK_MALLOC_H
#define LLVM_LIBC_SRC_STDLIB_OAK_OAK_MALLOC_H

#include "src/__support/macros/attributes.h"
#include "src/__support/macros/config.h"
#include "src/string/memory_utils/inline_memcpy.h"

#include <stddef.h>
#include <stdint.h>

namespace LIBC_NAMESPACE_DECL {
namespace oak {

// Vendor callbacks provided by the enclave application's Rust runtime. They
// bridge the C library's allocation functions to Rust's global allocator so
// that C and Rust code share a single heap (managed by
// `oak_enclave_runtime_support`), rather than the C library carving out its own
// static region.
//
// The signatures deliberately mirror Rust's `core::alloc::GlobalAlloc`: both
// the size and the alignment must be supplied on deallocation because that is
// what `GlobalAlloc::dealloc` (and the underlying `core::alloc::Layout`)
// requires. See
// <https://doc.rust-lang.org/core/alloc/trait.GlobalAlloc.html>.
//
// C's `free`/`realloc`, however, only receive a pointer. To reconcile the two
// models, every allocation is prefixed with an `AllocHeader` (see below) that
// records the exact size and alignment passed to Rust, so they can be replayed
// on free.
extern "C" {
// Allocates `size` bytes aligned to `alignment` (a power of two). Returns
// `nullptr` on failure. The `(size, alignment)` pair forms the Rust `Layout`.
void *__llvm_libc_malloc(size_t size, size_t alignment);

// Frees a block previously returned by `__llvm_libc_malloc`. The `size` and
// `alignment` must exactly match the values used to allocate it.
void __llvm_libc_free(void *ptr, size_t size, size_t alignment);
} // extern "C"

namespace internal {

// Bookkeeping stored immediately before every pointer handed to the caller.
// It captures everything required to reconstruct the Rust `Layout` on free and
// to copy the live bytes on realloc.
struct AllocHeader {
  void *base;        // Pointer actually returned by `__llvm_libc_malloc`.
  size_t total_size; // Total bytes requested from Rust (prefix + user bytes).
  size_t alignment;  // Alignment requested from Rust.
  size_t user_size;  // Bytes usable by the caller.
};

// The strictest fundamental alignment; `malloc`/`calloc`/`realloc` must return
// memory suitably aligned for any object (16 bytes on x86_64).
constexpr size_t DEFAULT_ALIGNMENT = alignof(max_align_t);

LIBC_INLINE size_t round_up(size_t value, size_t multiple) {
  return (value + multiple - 1) / multiple * multiple;
}

LIBC_INLINE AllocHeader *header_of(void *user_ptr) {
  return reinterpret_cast<AllocHeader *>(user_ptr) - 1;
}

} // namespace internal

// Allocates `size` bytes with at least `alignment` alignment (a value smaller
// than the fundamental alignment is rounded up). The returned pointer is
// preceded by an `internal::AllocHeader`.
LIBC_INLINE void *allocate(size_t size, size_t alignment) {
  using internal::AllocHeader;
  if (alignment < internal::DEFAULT_ALIGNMENT)
    alignment = internal::DEFAULT_ALIGNMENT;

  // Reserve enough space before the user pointer to hold the header while
  // keeping the user pointer aligned to `alignment`.
  const size_t prefix = internal::round_up(sizeof(AllocHeader), alignment);
  const size_t total = prefix + size;

  void *base = __llvm_libc_malloc(total, alignment);
  if (base == nullptr)
    return nullptr;

  void *user = static_cast<char *>(base) + prefix;
  AllocHeader *header = internal::header_of(user);
  header->base = base;
  header->total_size = total;
  header->alignment = alignment;
  header->user_size = size;
  return user;
}

// Frees a block previously returned by `allocate`. `nullptr` is ignored, as
// required by the C standard for `free`.
LIBC_INLINE void deallocate(void *user) {
  if (user == nullptr)
    return;
  internal::AllocHeader *header = internal::header_of(user);
  __llvm_libc_free(header->base, header->total_size, header->alignment);
}

// Resizes a block previously returned by `allocate`, preserving its alignment
// and copying the overlapping bytes. Mirrors C `realloc` semantics for the
// `nullptr` and zero-size edge cases.
LIBC_INLINE void *reallocate(void *user, size_t new_size) {
  if (user == nullptr)
    return allocate(new_size, internal::DEFAULT_ALIGNMENT);
  if (new_size == 0) {
    deallocate(user);
    return nullptr;
  }

  internal::AllocHeader *header = internal::header_of(user);
  const size_t old_size = header->user_size;
  const size_t alignment = header->alignment;

  void *new_user = allocate(new_size, alignment);
  if (new_user == nullptr)
    return nullptr;

  inline_memcpy(new_user, user, old_size < new_size ? old_size : new_size);
  deallocate(user);
  return new_user;
}

} // namespace oak
} // namespace LIBC_NAMESPACE_DECL

#endif // LLVM_LIBC_SRC_STDLIB_OAK_OAK_MALLOC_H

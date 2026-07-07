//===-- Implementation of calloc for Oak ----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdlib/calloc.h"
#include "src/__support/macros/config.h"
#include "src/stdlib/oak/oak_malloc.h"
#include "src/string/memory_utils/inline_memset.h"

#include <stddef.h>

namespace LIBC_NAMESPACE_DECL {

LLVM_LIBC_FUNCTION(void *, calloc, (size_t num, size_t size)) {
  size_t total;
  if (__builtin_mul_overflow(num, size, &total))
    return nullptr;
  void *ptr = oak::allocate(total, oak::internal::DEFAULT_ALIGNMENT);
  if (ptr != nullptr)
    inline_memset(ptr, 0, total);
  return ptr;
}

} // namespace LIBC_NAMESPACE_DECL

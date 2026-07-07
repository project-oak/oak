//===-- Implementation of free for Oak ------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdlib/free.h"
#include "src/__support/macros/config.h"
#include "src/stdlib/oak/oak_malloc.h"

namespace LIBC_NAMESPACE_DECL {

LLVM_LIBC_FUNCTION(void, free, (void *ptr)) { oak::deallocate(ptr); }

} // namespace LIBC_NAMESPACE_DECL

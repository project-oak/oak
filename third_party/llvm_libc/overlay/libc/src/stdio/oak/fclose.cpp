//===-- Implementation of fclose for Oak                   -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdio/fclose.h"

#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// Oak has no filesystem and therefore no `fopen`: the only `FILE`s that ever
// exist are the static standard-stream cookies (see `oak/file_internal.h`).
// Those are never dynamically allocated, so closing one is a no-op that always
// succeeds. Writes are unbuffered (see `fflush`), so there is nothing to flush
// on close either.
LLVM_LIBC_FUNCTION(int, fclose, (::FILE *)) { return 0; }

} // namespace LIBC_NAMESPACE_DECL

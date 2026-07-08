//===-- Implementation of fflush for Oak                   -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdio/fflush.h"

#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// Oak's stdio is unbuffered: `fwrite`/`fputs`/`fprintf` hand their bytes
// straight to the `__llvm_libc_stdio_write` vendor callback (see
// `oak/file_internal.h`). There is therefore never any buffered output to
// flush, for a specific stream or for all streams (`stream == nullptr`), so
// this always succeeds.
LLVM_LIBC_FUNCTION(int, fflush, (::FILE *)) { return 0; }

} // namespace LIBC_NAMESPACE_DECL

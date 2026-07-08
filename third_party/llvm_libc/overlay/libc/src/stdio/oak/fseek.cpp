//===-- Implementation of fseek for Oak                    -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdio/fseek.h"

#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// Oak's `FILE`s are non-seekable serial/channel streams backed by the
// `__llvm_libc_stdio_read`/`__llvm_libc_stdio_write` vendor callbacks (see
// `oak/file_internal.h`); there is no random-access filesystem. Seeking is
// therefore unsupported and always fails.
LLVM_LIBC_FUNCTION(int, fseek, (::FILE *, long, int)) { return -1; }

} // namespace LIBC_NAMESPACE_DECL

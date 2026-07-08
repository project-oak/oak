//===-- Implementation of ftell for Oak                    -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdio/ftell.h"

#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// Oak's `FILE`s are non-seekable serial/channel streams (see `fseek` and
// `oak/file_internal.h`); they have no meaningful, queryable file position, so
// reporting the offset always fails.
LLVM_LIBC_FUNCTION(long, ftell, (::FILE *)) { return -1; }

} // namespace LIBC_NAMESPACE_DECL

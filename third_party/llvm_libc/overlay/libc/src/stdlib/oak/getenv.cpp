//===-- Implementation of getenv for Oak                   -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/stdlib/getenv.h"

#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// The Oak enclave has no process environment: there is no `envp` passed to the
// entry point and no way to set variables. Every lookup therefore misses.
LLVM_LIBC_FUNCTION(char *, getenv, (const char *)) { return nullptr; }

} // namespace LIBC_NAMESPACE_DECL

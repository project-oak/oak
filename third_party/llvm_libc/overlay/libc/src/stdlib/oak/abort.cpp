//===-- Implementation of abort for Oak -----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// Oak's abort() is identical to baremetal's; re-export it rather than duplicate.
// Only the malloc family (see oak_malloc.h) is Oak-specific in stdlib.
#include "src/stdlib/baremetal/abort.cpp"

//===--- Helper functions for file I/O on Oak -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// Oak reuses baremetal's stdio helpers; re-export the header so the CMake
// header-library target keeps resolving. See third_party/llvm_libc/README.md.
#ifndef LLVM_LIBC_SRC_STDIO_OAK_FILE_INTERNAL_H
#define LLVM_LIBC_SRC_STDIO_OAK_FILE_INTERNAL_H

#include "src/stdio/baremetal/file_internal.h"

#endif // LLVM_LIBC_SRC_STDIO_OAK_FILE_INTERNAL_H

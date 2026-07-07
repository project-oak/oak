//===-- Implementation of remove for Oak ----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// Oak has no filesystem, so like baremetal remove() always fails; re-export it.
// See third_party/llvm_libc/README.md for the rationale.
#include "src/stdio/baremetal/remove.cpp"

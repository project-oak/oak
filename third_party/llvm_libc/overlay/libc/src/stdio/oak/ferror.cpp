//===-- Implementation of ferror for Oak                   -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// Oak's stdio is identical to baremetal; re-export it rather than duplicate.
// See third_party/llvm_libc/README.md for the rationale.
#include "src/stdio/baremetal/ferror.cpp"

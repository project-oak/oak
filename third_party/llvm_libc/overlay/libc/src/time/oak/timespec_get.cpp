//===-- Implementation of timespec_get for Oak ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// Oak's timespec_get is identical to baremetal: it delegates to the vendor
// callback `__llvm_libc_timespec_get_utc`, provided by the enclave runtime
// (`oak_enclave_runtime_support`). Re-export rather than duplicate.
// See third_party/llvm_libc/README.md for the rationale.
#include "src/time/baremetal/timespec_get.cpp"

//===-- Implementation of time for Oak                     -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "src/time/time_func.h"

#include "hdr/types/time_t.h"
#include "src/__support/common.h"
#include "src/__support/macros/config.h"

namespace LIBC_NAMESPACE_DECL {

// The Restricted Kernel exposes no wall-clock source (the
// `__llvm_libc_timespec_get_utc` vendor callback always reports failure, so
// `timespec_get` cannot help here). Reporting the epoch (0 =
// 1970-01-01T00:00:00Z) is safe for the current consumers: BoringSSL's X.509
// time verification is driven by the caller supplying an explicit comparison
// time via `X509_STORE_CTX_set_time`, so it never relies on `time(nullptr)`.
LLVM_LIBC_FUNCTION(time_t, time, (time_t * tp)) {
  if (tp != nullptr)
    *tp = 0;
  return 0;
}

} // namespace LIBC_NAMESPACE_DECL

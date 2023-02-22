// Copyright 2021 The IREE Authors
//
// Licensed under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// A example of static library loading in IREE. See the README.md for more info.
// Note: this demo requires artifacts from iree-compile before it will run.

#ifndef CC_IREE_H_
#define CC_IREE_H_

#include <stddef.h>
#include <stdint.h>

// #define stderr 2
export extern const int stderr = 2;

#ifdef __cplusplus
extern "C" {
#endif

int iree_init();

int iree_run(const uint8_t* input_bytes_ptr, size_t input_bytes_len, uint8_t* output_bytes_ptr,
             size_t* output_bytes_len_ptr);

void print_output_tensors(uint8_t* output_bytes_ptr, size_t output_bytes_len);

#ifdef __cplusplus
}
#endif

#endif  // CC_IREE_H_
/*
 * Copyright 2023 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef CC_IREE_IREE_H_
#define CC_IREE_IREE_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

int iree_init(size_t* expected_output_bytes_len_ptr);

int iree_run(const uint8_t* input_bytes_ptr, size_t input_bytes_len, uint8_t* output_bytes_ptr,
             size_t* output_bytes_len_ptr);

void iree_cleanup();

#ifdef __cplusplus
}
#endif

#endif  // CC_IREE_IREE_H_

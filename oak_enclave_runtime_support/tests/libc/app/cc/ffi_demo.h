/*
 * Copyright 2026 The Project Oak Authors
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

#ifndef OAK_FFI_TEST_APP_FFI_DEMO_H_
#define OAK_FFI_TEST_APP_FFI_DEMO_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/// Allocates a buffer and constructs a greeting string for the given name.
/// The returned pointer must be freed with `free_greeting()`.
/// Returns NULL if memory allocation fails.
char *create_greeting(const char *name);

/// Frees a greeting previously returned by `create_greeting()`.
void free_greeting(char *greeting);

/// Fills `buf` with a test pattern and returns a checksum.
/// Demonstrates nontrivial memory operations.
unsigned int fill_and_checksum(void *buf, size_t len);

#ifdef __cplusplus
}
#endif

#endif  // OAK_FFI_TEST_APP_FFI_DEMO_H_

/*
 * Copyright 2022 The Project Oak Authors
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

#include <stddef.h>

extern "C" {
void *memset_avx2(void *str, int c, size_t n);
void *memset_generic(void *str, int c, size_t n);

void *memset(void *str, int c, size_t n) {
  // Use more performnat memset_avx2 over sse2 memset_generic.
  return memset_avx2(str, c, n);
}

void* __memset_chk_fail(
    void* /*dst*/, int /*byte*/,
    size_t /*count*/, size_t /*dst_len*/) {
  // TODO: bark by showing an error or bite by raising a panic.
  return nullptr;
}
}

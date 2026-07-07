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

#include "ffi_demo.h"

#include <stdlib.h>
#include <string.h>

char* create_greeting(const char* name) {
  const char* prefix = "Hello from C, ";
  size_t prefix_len = strlen(prefix);
  size_t name_len = strlen(name);
  size_t total = prefix_len + name_len + 1;

  char* buf = (char*)malloc(total);
  if (!buf) {
    return NULL;
  }

  memcpy(buf, prefix, prefix_len);
  memcpy(buf + prefix_len, name, name_len);
  buf[total - 1] = '\0';
  return buf;
}

void free_greeting(char* greeting) { free(greeting); }

unsigned int fill_and_checksum(void* buf, size_t len) {
  unsigned char* bytes = (unsigned char*)buf;
  unsigned int checksum = 0;

  /* Fill with a deterministic pattern. */
  for (size_t i = 0; i < len; i++) {
    bytes[i] = (unsigned char)(i * 7 + 13);
  }

  /* Compute a simple checksum. */
  for (size_t i = 0; i < len; i++) {
    checksum = checksum * 31 + bytes[i];
  }

  return checksum;
}

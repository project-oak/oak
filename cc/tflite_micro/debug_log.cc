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

#include <cstdio>
#include <cstring>

#include "tflite_micro.h"

extern "C" void DebugLog(const char* s) {
  // oak_log_debug is an explicitly defined symbol (T)
  // in Oak tensorflow freestanding binary, while it's
  // an undefined symbol (w) in Linux freestanding binary.
  if (oak_log_debug) {
    oak_log_debug(s, strlen(s));
  }
}

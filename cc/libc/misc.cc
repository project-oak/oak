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

#if !defined(TF_LITE_STRIP_ERROR_STRINGS)
void MicroPrintf(const char* format, ...);
#else
#define MicroPrintf(...)
#endif

extern "C" {
// Used by flexbuffers::Reference::AsInt64() and
// flexbuffers::Reference::AsUInt64() in TFLM.
int* __errno_location() {
  // Oak supports only single-threading for the moment
  // hence one errno singleton instance is used.
  static int errno = 0;
  return &errno;
}

// Used in flatbuffers and gemmlowp/fixedpoint headers
// when optimization is disabled (--define no_opt=1).
void __assert_fail(const char* assertion, const char* file, unsigned int line,
                   const char* function) {
  MicroPrintf("%s in %s:%d %s", assertion, file, line, function);
}

// Used in TFLM types and runtime_shape header files.
void abort() {
  MicroPrintf("Aborting...");

  // abort is a 'noreturn' function.
  while (1)
    ;
}

// *NOT* used when linking to Oak Kernel/Runtime since
// this function is simply used to build a freestanding
// program binary runnable and debuggable locally.
int atexit(void (*)()) { return 0; }
}

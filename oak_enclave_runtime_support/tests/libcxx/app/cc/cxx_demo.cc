// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// C++ test library for Oak Restricted Kernel FFI.
//
// Exercises C++ standard library features (containers, algorithms, smart
// pointers, strings) inside an enclave linked against LLVM libc and libc++.

#include "cxx_demo.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <algorithm>
#include <array>
#include <memory>
#include <numeric>
#include <string>
#include <vector>

extern "C" void cxx_sort_array(int32_t* data, size_t len) {
  std::sort(data, data + len);
}

extern "C" int64_t cxx_vector_sum(size_t count) {
  std::vector<int64_t> v;
  v.reserve(count);
  for (size_t i = 0; i < count; ++i) {
    v.push_back(static_cast<int64_t>(i));
  }
  return std::accumulate(v.begin(), v.end(), int64_t{0});
}

extern "C" char* cxx_format_greeting(const char* name) {
  std::string greeting = "Hello, ";
  greeting += name;
  greeting += "!";

  // Copy into a malloc'd buffer for the caller.
  char* result = static_cast<char*>(malloc(greeting.size() + 1));
  if (result) {
    memcpy(result, greeting.c_str(), greeting.size() + 1);
  }
  return result;
}

extern "C" void cxx_free_string(char* s) { free(s); }

extern "C" int32_t cxx_unique_ptr_test(int32_t value) {
  auto ptr = std::make_unique<int32_t>(value);
  *ptr *= 2;
  return *ptr;
  // ptr is automatically freed here.
}

extern "C" void cxx_stdio_test() {
  // fprintf exercises the vfprintf FILE path; fwrite exercises the raw FILE
  // write path. Both funnel through the Oak libc's __llvm_libc_stdio_write
  // vendor callback to the RK write syscall (fd 2 -> serial console).
  fprintf(stderr, "cxx fprintf test passed\n");
  const char msg[] = "cxx fwrite test passed\n";
  fwrite(msg, 1, sizeof(msg) - 1, stderr);
}

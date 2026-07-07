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
// Demonstrates that C++ standard library features (containers, algorithms,
// smart pointers, strings) work inside an enclave application linked against
// LLVM libc and libc++.
//
// All functions use a C linkage (`extern "C"`) so they can be called from
// Rust via FFI without name mangling.

#ifndef OAK_ENCLAVE_RUNTIME_SUPPORT_TESTS_LIBCXX_APP_CC_CXX_DEMO_H_
#define OAK_ENCLAVE_RUNTIME_SUPPORT_TESTS_LIBCXX_APP_CC_CXX_DEMO_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// Sorts an array of int32_t values in ascending order using std::sort.
void cxx_sort_array(int32_t* data, size_t len);

// Pushes `count` elements (0..count-1) to a std::vector, sums them, and
// returns the total.  Exercises heap allocation via std::vector.
int64_t cxx_vector_sum(size_t count);

// Allocates a std::string, formats "Hello, <name>!" into it, copies the
// result into a malloc'd C buffer, and returns it.  The caller must free
// the returned pointer with cxx_free_string().
char* cxx_format_greeting(const char* name);

// Frees a string returned by cxx_format_greeting().
void cxx_free_string(char* s);

// Exercises std::unique_ptr: creates an int on the heap, doubles it,
// and returns the result.  The smart pointer auto-frees the allocation.
int32_t cxx_unique_ptr_test(int32_t value);

// Exercises the C FILE* stdio path by writing marker lines to stderr with
// fprintf and fwrite.  The Oak libc routes these through the
// __llvm_libc_stdio_write vendor callback to the Restricted Kernel write
// syscall, which sends them to the serial console.
void cxx_stdio_test(void);

#ifdef __cplusplus
}
#endif

#endif  // OAK_ENCLAVE_RUNTIME_SUPPORT_TESTS_LIBCXX_APP_CC_CXX_DEMO_H_

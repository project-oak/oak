/*
 * Copyright 2025 The Project Oak Authors
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

#ifndef CC_FFI_CXX_STRING_H_
#define CC_FFI_CXX_STRING_H_

#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>

namespace oak::ffi {

// A wrapper around a std::string so that it can be passed to Rust.
//
// To use it, create an instance and then modify the contents of the string
// pointer to contain the desired content. Then you can return this to rust.
//
// Example of returing a serialized proto to Rust:
//
// MyProto proto = DoSomething();
//
// CxxString result;
// proto.SerializeToString(result.str);
// return result;
class CxxString {
 public:
  CxxString() = default;
  CxxString(const CxxString&) = delete;
  CxxString& operator=(const CxxString&) = delete;
  CxxString(CxxString&&) = default;
  CxxString& operator=(CxxString&&) = default;

  std::string* string() {
    assert(str_ != nullptr);
    return str_;
  }

 private:
  std::string* str_ = new std::string();
};  // namespace oak::ffi

extern "C" {
// Return the raw pointer to the underlying string data.
char* cxx_string_data(CxxString* str);

// Return the length of the underlying data.
size_t cxx_string_len(CxxString* str);

// Free the string.
void free_cxx_string(CxxString* str);
}

}  // namespace oak::ffi

#endif  // CC_FFI_CXX_STRING_H_

//
// Copyright 2025 The Project Oak Authors
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
//

/// A basic wrapper around Rust or C-provided bytes of known length.
///
/// This structure can be passed back and forth between Rust and C code.
/// Functions that use the type should explain the lifetime expectations for the
/// type.

#include <iostream>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/bytes_bindings.h"
#include "cc/ffi/cxx_string.h"

extern "C" oak::ffi::CxxString create_test_string(
    oak::ffi::bindings::BytesView name) {
  oak::ffi::CxxString result;
  *(result.string()) =
      absl::StrCat("Hello from FFI, ", absl::string_view(name));
  return result;
}

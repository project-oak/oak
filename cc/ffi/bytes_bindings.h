/*
 * Copyright 2024 The Project Oak Authors
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

#ifndef CC_FFI_BYTES_BINDINGS_H_
#define CC_FFI_BYTES_BINDINGS_H_

#include <cstdint>

#include "absl/strings/string_view.h"

namespace oak::ffi::bindings {
// A struct holding a sequence of Bytes allocated in Rust.
// Corresponds to RustBytes struct in oak_session/ffi/types.rs
//
// C/C++ that receives an instance of this as a return value from Rust will be
// expected to free it, either by calling `free_rust_bytes_contents`, or by
// passing the bytes back to Rust as an argument to a function that specifies in
// the documentation that it will re-claim ownership of the parameter.
struct RustBytes {
  const char* data;
  uint64_t len;

  operator absl::string_view() { return absl::string_view(data, len); }
};

// A borrowed view of bytes from either C or Rust.
//
// Functions that use or return BytesView structures should document the
// lifetime expectations of the view.
//
// Corresponds to BytesView struct in oak_session/ffi/types.rs
struct BytesView {
  const char* data;
  uint64_t len;

  explicit BytesView(absl::string_view bytes);
  explicit BytesView(RustBytes bytes);
};

extern "C" {
extern void free_rust_bytes(RustBytes*);
extern void free_rust_bytes_contents(RustBytes);
}

}  // namespace oak::ffi::bindings

#endif  // CC_FFI_BYTES_BINDINGS_H_

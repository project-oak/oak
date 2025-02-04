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

#include <utility>

#include "absl/strings/string_view.h"
#include "cc/oak_session/oak_session_bindings.h"

#ifndef CC_OAK_SESSION_RUST_BYTES_H_
#define CC_OAK_SESSION_RUST_BYTES_H_

namespace oak::session {

// A wrapper around Rust-allocated byte sequences.
//
// This type wraps a heap-allocated sequence of bytes (a boxed slice) that Rust
// has provided to C++ code for usage for an indeterminate amount of time.
//
// This wraper class takes care to ensure that the Rust memory is freed once the
// C++ code is finished using it.
//
// The type has move semantics similar to a std::unique_ptr - you can move
// ownership around, but there can only be one owner at a time.
class RustBytes {
 public:
  explicit RustBytes(bindings::RustBytes* ffi_rust_bytes)
      : ffi_rust_bytes_(ffi_rust_bytes) {}

  RustBytes(const RustBytes&) = delete;
  RustBytes& operator=(const RustBytes&) = delete;

  RustBytes(RustBytes&& other)
      // Take ownership of the underlying pointer, and null out the source
      // pointer so that we don't attempt to free it multiple times.
      : ffi_rust_bytes_(std::exchange(other.ffi_rust_bytes_, nullptr)) {}

  RustBytes& operator=(RustBytes&& other) {
    // Take ownership of the underlying pointer, and null out the source
    // pointer so that we don't attempt to free it multiple times.
    ffi_rust_bytes_ = other.ffi_rust_bytes_;
    other.ffi_rust_bytes_ = nullptr;
    return *this;
  }

  ~RustBytes() {
    // When move occurs, we reset the source to nullptr; so of course don't try
    // to free that.
    if (ffi_rust_bytes_ != nullptr) {
      bindings::free_rust_bytes(ffi_rust_bytes_);
    }
  }

  operator absl::string_view() {
    return static_cast<absl::string_view>(*ffi_rust_bytes_);
  }

 private:
  bindings::RustBytes* ffi_rust_bytes_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_RUST_BYTES_H_

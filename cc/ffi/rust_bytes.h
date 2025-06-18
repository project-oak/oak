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

#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/bytes_bindings.h"
#include "cc/ffi/error_bindings.h"

#ifndef CC_OAK_SESSION_RUST_BYTES_H_
#define CC_OAK_SESSION_RUST_BYTES_H_

namespace oak::ffi {

// A wrapper around Rust-allocated byte sequences.
//
// This type wraps a heap-allocated sequence of bytes (a boxed slice) that Rust
// has provided to C++ code for usage for an indeterminate amount of time.
//
// This wrapper class takes care to ensure that the Rust memory is freed once
// the C++ code is finished using it.
//
// The type contains convenience conversions to make it easy to convert it to an
// `absl::string_view` for use in cases where that parameter type is expected.
//
// If you want to take ownership of the memory, you can copy it into a
// `std::string` using the explicit `std::string` conversion operator provided.
//
// The type has move semantics similar to a std::unique_ptr - you can move
// ownership around, but there can only be one owner at a time.
class RustBytes {
 public:
  explicit RustBytes(ffi::bindings::RustBytes* ffi_rust_bytes)
      : ffi_rust_bytes_(ffi_rust_bytes) {}

  RustBytes(const RustBytes&) = delete;
  RustBytes& operator=(const RustBytes&) = delete;

  RustBytes(RustBytes&& other)
      // Take ownership of the underlying pointer, and null out the source
      // pointer so that we don't attempt to free it multiple times.
      : ffi_rust_bytes_(std::exchange(other.ffi_rust_bytes_, nullptr)) {}

  RustBytes& operator=(RustBytes&& other) {
    if (this == &other) return *this;
    if (ffi_rust_bytes_ != nullptr) {
      ffi::bindings::free_rust_bytes(ffi_rust_bytes_);
    }
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
      ffi::bindings::free_rust_bytes(ffi_rust_bytes_);
    }
  }

  // Expose the underlying Rust bytes as an absl::string_view.
  //
  // This conversion operator allows the RustBytes type to be used, for
  // example, as a function parameter in a position that's expected
  // absl::string_view.
  //
  // No copy of the underlying data will occur.
  operator absl::string_view() const {
    return static_cast<absl::string_view>(*ffi_rust_bytes_);
  }

  // Copy the underlying Rust bytes into a new std::string in the C++ memory
  // space.
  explicit operator std::string() const {
    return std::string(ffi_rust_bytes_->data, ffi_rust_bytes_->len);
  }

 private:
  ffi::bindings::RustBytes* ffi_rust_bytes_;
};

inline bool operator==(const RustBytes& lhs, absl::string_view rhs) {
  return static_cast<absl::string_view>(lhs) == rhs;
}

// A convenience function to create a new absl::StatusOr<RustBytes> instance
// containing a message populated from the provided error, taking ownership
// of all related pointers.
inline absl::StatusOr<std::optional<RustBytes>> ErrorIntoRustBytes(
    ffi::bindings::ErrorOrRustBytes&& error_or_rust_bytes) {
  if (error_or_rust_bytes.error != nullptr) {
    return ffi::bindings::ErrorIntoStatus(error_or_rust_bytes.error);
  }

  if (error_or_rust_bytes.result == nullptr) return std::nullopt;

  return RustBytes(error_or_rust_bytes.result);
}

}  // namespace oak::ffi

#endif  // CC_OAK_SESSION_RUST_BYTES_H_

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

#ifndef CC_FFI_BYTES_VIEW_H_
#define CC_FFI_BYTES_VIEW_H_

#include <cstdint>

#include "absl/strings/string_view.h"

namespace oak::ffi::bindings {

// A borrowed view of bytes from either C or Rust.
//
// Functions that use or return BytesView structures should document the
// lifetime expectations of the view.
//
// Corresponds to BytesView struct in oak_session/ffi/types.rs
struct BytesView {
  const char* data;
  // Rust usize is not always the same as size_t, but always matches uintptr_t.
  // https://internals.rust-lang.org/t/pre-rfc-usize-is-not-size-t/15369
  uintptr_t len;

  explicit BytesView(absl::string_view bytes)
      : data(bytes.data()), len(bytes.size()) {}

  operator absl::string_view() { return absl::string_view(data, len); }
};

}  // namespace oak::ffi::bindings

#endif  // CC_FFI_BYTES_VIEW_H_

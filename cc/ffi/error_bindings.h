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

#ifndef CC_FFI_ERROR_BINDINGS_H_
#define CC_FFI_ERROR_BINDINGS_H_

#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "cc/ffi/bytes_bindings.h"

namespace oak::ffi::bindings {
// Corresponds to Error struct in oak_session/ffi/types.rs
struct Error {
  ffi::bindings::RustBytes message;
};

// Corresponds to ErrorOrBytes struct in oak_session/ffi/types.rs
struct ErrorOrRustBytes {
  ffi::bindings::RustBytes* result;
  Error* error;
};

extern "C" {
extern void free_error(Error*);
}

// A convenience function to create a new absl::Status instance containing a
// message populated from the provided error.
//
// The error will be released.
absl::Status ErrorIntoStatus(bindings::Error* error);

}  // namespace oak::ffi::bindings

#endif  // CC_FFI_ERROR_BINDINGS_H_

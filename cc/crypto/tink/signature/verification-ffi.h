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

#ifndef CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_FFI_H_
#define CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_FFI_H_

#include <stddef.h>
#include <stdint.h>

#include "cc/ffi/bytes_view.h"
#include "cc/ffi/cxx_string.h"

extern "C" {

// Wrapper around absl::Status to pass information across the FFI boundary.
// This wrapper will be replaced once the bindings around absl::Status are
// complete.
struct StatusWrapper {
  // Equivalent to absl::StatusCode. See
  // https://github.com/abseil/abseil-cpp/blob/8b2b78bb9bc570ea422fc891392d2ebdb35468b1/absl/status/status.h#L99
  int status_code;
  // Status message. This is meant to resemble the absl::Status message()
  // function:
  // https://github.com/abseil/abseil-cpp/blob/8b2b78bb9bc570ea422fc891392d2ebdb35468b1/absl/status/status.h#L501-L507C21
  oak::ffi::CxxString status_message;
};

// Takes a message, a message signature, and a proto serialized Tink keyset
// handle, and verifies whether the signature was issued by the serialized
// keyset handle. The response is a CxxString encapsulation of a VerifyStatus
// proto.
// Note: The Tink keyset handle must not contain any secret key material.
struct StatusWrapper VerifySignatureWithTink(
    oak::ffi::bindings::BytesView message,
    oak::ffi::bindings::BytesView signature,
    oak::ffi::bindings::BytesView ca_public_keyset);

}  // extern C

#endif  // CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_FFI_H_

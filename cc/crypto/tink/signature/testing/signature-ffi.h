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

#ifndef CC_CRYPTO_TINK_SIGNATURE_TESTING_SIGNATURE_FFI_H_
#define CC_CRYPTO_TINK_SIGNATURE_TESTING_SIGNATURE_FFI_H_

#include <stddef.h>
#include <stdint.h>

#include "cc/ffi/bytes_view.h"
#include "cc/ffi/cxx_string.h"

extern "C" {

// Wrapper around absl::StatusOr<SignatureWrapper> to pass information across
// the FFI boundary.
struct SignatureStatusWrapper {
  int status_code;
  oak::ffi::CxxString status_message;

  oak::ffi::CxxString signature;
  oak::ffi::CxxString tink_public_keyset;
};

// Generates a new keypair with Tink, and signs the message with that keypair.
// Returns an FFI-compatible struct containing the status of this operation, and
// the signature (and public verifying key) if it was successful.
struct SignatureStatusWrapper SignWithTink(
    oak::ffi::bindings::BytesView message);

}  // extern C

#endif  // CC_CRYPTO_TINK_SIGNATURE_TESTING_SIGNATURE_FFI_H_

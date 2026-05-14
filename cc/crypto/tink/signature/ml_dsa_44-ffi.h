/*
 * Copyright 2026 The Project Oak Authors
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

#ifndef CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_FFI_H_
#define CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_FFI_H_

#include <stddef.h>
#include <stdint.h>

#include "cc/crypto/tink/signature/verification-ffi.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/cxx_string.h"

extern "C" {

// Verifies an ML-DSA-44 signature using raw key bytes.
// Returns StatusWrapper with status_code 0 on success.
struct StatusWrapper MlDsa44Verify(
    oak::ffi::bindings::BytesView message,
    oak::ffi::bindings::BytesView signature,
    oak::ffi::bindings::BytesView raw_public_key);

// Result of an ML-DSA-44 signing operation.
struct MlDsa44SignResult {
  int status_code;
  oak::ffi::CxxString status_message;
  // The raw 2420-byte signature on success.
  oak::ffi::CxxString signature;
};

// Signs a message with ML-DSA-44 using raw key bytes.
struct MlDsa44SignResult MlDsa44Sign(
    oak::ffi::bindings::BytesView message,
    oak::ffi::bindings::BytesView raw_private_key,
    oak::ffi::bindings::BytesView raw_public_key);

// Result of an ML-DSA-44 key generation operation.
struct MlDsa44KeyGenResult {
  int status_code;
  oak::ffi::CxxString status_message;
  // The raw public key (1312 bytes) on success.
  oak::ffi::CxxString public_key;
  // The raw private key on success.
  oak::ffi::CxxString private_key;
};

// Generates an ML-DSA-44 keypair.
struct MlDsa44KeyGenResult MlDsa44KeyGen();

}  // extern C

#endif  // CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_FFI_H_

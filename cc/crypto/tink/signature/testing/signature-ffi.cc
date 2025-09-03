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

#include "cc/crypto/tink/signature/testing/signature-ffi.h"

#include "absl/status/statusor.h"
#include "cc/crypto/tink/signature/testing/signature_utils.h"
#include "cc/ffi/bytes_view.h"

using ::oak::ffi::bindings::BytesView;

extern "C" {

SignatureStatusWrapper SignWithTink(BytesView message) {
  absl::StatusOr<oak::crypto::tink::SignatureWrapper> signature_wrapper =
      oak::crypto::tink::SignWithTink(message);

  SignatureStatusWrapper sign_status;
  sign_status.status_code = static_cast<int>(signature_wrapper.status().code());
  *sign_status.status_message.string() = signature_wrapper.status().message();
  if (signature_wrapper.ok()) {
    *sign_status.signature.string() = signature_wrapper->signature;
    *sign_status.tink_public_keyset.string() =
        signature_wrapper->tink_public_keyset;
  }
  return sign_status;
}

}  // extern C

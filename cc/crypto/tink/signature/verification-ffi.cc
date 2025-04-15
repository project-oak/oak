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

#include "cc/crypto/tink/signature/verification-ffi.h"

#include <stddef.h>
#include <stdint.h>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/tink/signature/verification_utils.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/cxx_string.h"

namespace oak::crypto::tink {

using ::oak::ffi::CxxString;
using ::oak::ffi::bindings::BytesView;

extern "C" {

StatusWrapper VerifySignatureWithTink(BytesView message, BytesView signature,
                                      BytesView ca_public_keyset) {
  absl::Status signature_verification =
      VerifyTinkDigitalSignature(message, signature, ca_public_keyset);

  StatusWrapper verify_status;
  verify_status.status_code = static_cast<int>(signature_verification.code());
  *verify_status.status_message.string() = signature_verification.message();
  return verify_status;
}
}  // extern C

}  // namespace oak::crypto::tink

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

#ifndef CC_CRYPTO_TINK_SIGNATURE_SIGNATURE_UTILS_H_
#define CC_CRYPTO_TINK_SIGNATURE_SIGNATURE_UTILS_H_

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace oak::crypto::tink {

struct SignatureWrapper {
  // The signature.
  std::string signature;
  // The proto serialized Tink public keyset that can be used to verify the
  // signature.
  std::string tink_public_keyset;
};

// Generates a new keypair with Tink, and signs the message with that keypair.
// Returns a struct containing the signature (and public verifying key).
absl::StatusOr<SignatureWrapper> SignWithTink(absl::string_view message);

}  // namespace oak::crypto::tink

#endif  // CC_CRYPTO_TINK_SIGNATURE_SIGNATURE_UTILS_H_

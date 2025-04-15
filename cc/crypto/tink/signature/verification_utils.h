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

#ifndef CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_UTILS_H_
#define CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_UTILS_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"

namespace oak::crypto::tink {

// Parses the proto serialized keyset, and validates that the signed information
// was signed by the serialized keyset using Tink's Digital Signature library
// https://developers.google.com/tink/digital-signature.
absl::Status VerifyTinkDigitalSignature(
    absl::string_view message, absl::string_view signature,
    absl::string_view proto_serialized_keyset);

}  // namespace oak::crypto::tink

#endif  // CC_CRYPTO_TINK_SIGNATURE_VERIFICATION_UTILS_H_

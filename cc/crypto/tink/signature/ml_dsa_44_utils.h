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

#ifndef CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_UTILS_H_
#define CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_UTILS_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace oak::crypto::tink {

// An ML-DSA-44 keypair containing raw key bytes.
struct MlDsa44KeyPair {
  // The raw public key (1312 bytes).
  std::string public_key;
  // The raw private key seed (not the full expanded private key).
  std::string private_key;
};

// Verifies an ML-DSA-44 signature using raw key bytes.
// raw_public_key must be exactly 1312 bytes.
// signature must be exactly 2420 bytes.
absl::Status VerifyMlDsa44(absl::string_view message,
                            absl::string_view signature,
                            absl::string_view raw_public_key);

// Signs a message using an ML-DSA-44 key pair.
// Returns the raw 2420-byte signature.
absl::StatusOr<std::string> SignMlDsa44(absl::string_view message,
                                        const MlDsa44KeyPair& key_pair);

// Generates an ML-DSA-44 keypair.
// Returns an MlDsa44KeyPair containing the raw public key (1312 bytes) and the
// raw private key.
absl::StatusOr<MlDsa44KeyPair> GenerateMlDsa44KeyPair();

}  // namespace oak::crypto::tink

#endif  // CC_CRYPTO_TINK_SIGNATURE_ML_DSA_44_UTILS_H_

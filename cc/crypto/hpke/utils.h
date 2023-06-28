/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_CRYPTO_HPKE_CONSTANTS_H_
#define CC_CRYPTO_HPKE_CONSTANTS_H_

#include <memory>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/aead.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Helpful struct for keeping track of key information returned from the BoringSSL HPKE library.
struct KeyInfo {
  size_t key_size;
  std::vector<uint8_t> key_bytes;
};

// Generate response key for the response context.
absl::StatusOr<std::unique_ptr<EVP_AEAD_CTX>> GetResponseContext(EVP_HPKE_CTX* hpke_ctx);

// Generate a base nonce for the AEAD response context.
absl::StatusOr<std::vector<uint8_t>> GetResponseBaseNonce(EVP_HPKE_CTX* ctx);

// Determines current nonce from the sequence number and the base nonce. This is needed for AEAD
// response encryption. This is the same nonce computation as for HPKE to ensure nonce uniqueness.
// It is up to the caller to increment the sequence number after calling the function.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
std::vector<uint8_t> CalculateNonce(const std::vector<uint8_t>& base_nonce,
                                    uint64_t sequence_number);

absl::StatusOr<uint64_t> IncrementSequenceNumber(uint64_t sequence_number);

}  // namespace oak::crypto
#endif  // CC_CRYPTO_HPKE_CONSTANTS_H_

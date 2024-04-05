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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/aead.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Helpful struct for keeping track of key information returned from the
// BoringSSL HPKE library.
struct KeyInfo {
  size_t key_size;
  std::vector<uint8_t> key_bytes;
};

// Generate session key for the AEAD context.
absl::StatusOr<std::unique_ptr<EVP_AEAD_CTX>> GetContext(
    EVP_HPKE_CTX* hpke_ctx, absl::string_view key_context_string);

// Generates random nonce for AEAD.
// RFC 9180 uses deterministic nonces which leads to the possibility of the
// following attack:
// - An attacker can record a client request and wait until the application
// database changes
//   - I.e. it updates an internal lookup database based on the public data
// - Then if an attacker replays the same request it can get a different
// response encrypted with the same nonce
//   - And having 2 different messages encrypted with the same nonce breaks
//   AES-GCM
//     - The attack is called AES-GCM Forbidden Attack
// To mitigate the AES-GCM Forbidden Attack Oak is using random nonces for
// encrypting messages with AEAD.
absl::StatusOr<std::vector<uint8_t>> GenerateRandomNonce();

// Encrypts `plaintext` and authenticates `associated_data` using AEAD with
// `context` and `nonce`.
absl::StatusOr<std::string> AeadSeal(const EVP_AEAD_CTX* context,
                                     std::vector<uint8_t> nonce,
                                     absl::string_view plaintext,
                                     absl::string_view associated_data);

// Decrypts `ciphertext` and authenticates `associated_data` using AEAD using
// `context` and `nonce`.
absl::StatusOr<std::string> AeadOpen(const EVP_AEAD_CTX* context,
                                     std::vector<uint8_t> nonce,
                                     absl::string_view ciphertext,
                                     absl::string_view associated_data);

}  // namespace oak::crypto
#endif  // CC_CRYPTO_HPKE_CONSTANTS_H_

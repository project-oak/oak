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

#ifndef CC_CRYPTO_HPKE_SENDER_CONTEXT_H_
#define CC_CRYPTO_HPKE_SENDER_CONTEXT_H_

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Context for generating encrypted requests to the recipient and for decrypting
// encrypted responses from the recipient. This is based on bi-directional
// encryption using AEAD.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>.
class SenderContext {
 public:
  SenderContext(std::vector<uint8_t> encapsulated_public_key,
                std::unique_ptr<EVP_AEAD_CTX> request_aead_context,
                std::unique_ptr<EVP_AEAD_CTX> response_aead_context)
      : serialized_encapsulated_public_key_(encapsulated_public_key.begin(),
                                            encapsulated_public_key.end()),
        request_aead_context_(std::move(request_aead_context)),
        response_aead_context_(std::move(response_aead_context)) {}

  std::string GetSerializedEncapsulatedPublicKey() const {
    return serialized_encapsulated_public_key_;
  }

  // Encrypts message with associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> Seal(const std::vector<uint8_t>& nonce,
                                   absl::string_view plaintext,
                                   absl::string_view associated_data);

  // Decrypts response message and validates associated data using AEAD as part
  // of bidirectional communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> Open(const std::vector<uint8_t>& nonce,
                                   absl::string_view ciphertext,
                                   absl::string_view associated_data);

  ~SenderContext();

 private:
  std::string serialized_encapsulated_public_key_;
  std::unique_ptr<EVP_AEAD_CTX> request_aead_context_;
  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_;
};

// Sets up an HPKE sender by generating an ephemeral keypair (and serializing
// the corresponding public key) and creating a sender context. Returns the
// encapsulated public key, sender request and sender response contexts.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
//
// Encapsulated public key is represented as a NIST P-256 SEC1 encoded point
// public key. <https://secg.org/sec1-v2.pdf>
absl::StatusOr<std::unique_ptr<SenderContext>> SetupBaseSender(
    absl::string_view serialized_recipient_public_key, absl::string_view info);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_HPKE_SENDER_CONTEXT_H_

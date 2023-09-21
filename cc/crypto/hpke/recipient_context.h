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

#ifndef CC_CRYPTO_HPKE_RECIPIENT_CONTEXT_H_
#define CC_CRYPTO_HPKE_RECIPIENT_CONTEXT_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"

namespace oak::crypto {

struct KeyPair {
  std::string private_key;
  std::string public_key;

  // Generates a KeyPair that the recipient can use for HPKE.
  static absl::StatusOr<KeyPair> Generate();
};

class RecipientContext {
 public:
  RecipientContext(std::unique_ptr<EVP_AEAD_CTX> request_aead_context,
                   std::vector<uint8_t> request_base_nonce, uint64_t request_sequence_number,
                   std::unique_ptr<EVP_AEAD_CTX> response_aead_context,
                   std::vector<uint8_t> response_base_nonce, uint64_t response_sequence_number)
      : request_aead_context_(std::move(request_aead_context)),
        request_base_nonce_(request_base_nonce),
        request_sequence_number_(request_sequence_number),
        response_aead_context_(std::move(response_aead_context)),
        response_base_nonce_(response_base_nonce),
        response_sequence_number_(response_sequence_number) {}

  // Decrypts message and validates associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> Open(absl::string_view ciphertext, absl::string_view associated_data);

  // Encrypts response message with associated data using AEAD as part of bidirectional
  // communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> Seal(absl::string_view plaintext, absl::string_view associated_data);

  ~RecipientContext();

 private:
  std::unique_ptr<EVP_AEAD_CTX> request_aead_context_;
  std::vector<uint8_t> request_base_nonce_;
  uint64_t request_sequence_number_;

  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_;
  std::vector<uint8_t> response_base_nonce_;
  uint64_t response_sequence_number_;
};

// Sets up an HPKE recipient by creating a recipient context.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
absl::StatusOr<std::unique_ptr<RecipientContext>> SetupBaseRecipient(
    absl::string_view serialized_encapsulated_public_key, const KeyPair& recipient_key_pair,
    absl::string_view info);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_HPKE_RECIPIENT_CONTEXT_H_

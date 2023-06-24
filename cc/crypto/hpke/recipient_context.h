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
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/utils.h"
#include "openssl/hpke.h"

namespace oak::crypto {

struct KeyPair {
  std::string private_key;
  std::string public_key;

  // Generates a KeyPair that the recipient and sender can use for HPKE.
  static absl::StatusOr<KeyPair> Generate();
};

class RecipientRequestContext {
 public:
  RecipientRequestContext(std::unique_ptr<EVP_HPKE_CTX> hpke_context)
      : hpke_context_(std::move(hpke_context)) {}
  // Decrypts message and validates associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> Open(absl::string_view ciphertext, absl::string_view associated_data);
  ~RecipientRequestContext();

 private:
  std::unique_ptr<EVP_HPKE_CTX> hpke_context_;
};

class RecipientResponseContext {
 public:
  RecipientResponseContext(std::unique_ptr<EVP_AEAD_CTX> aead_response_context,
                           std::vector<uint8_t> response_nonce)
      : aead_response_context_(std::move(aead_response_context)), response_nonce_(response_nonce){};
  // Encrypts response message with associated data using AEAD as part of bidirectional
  // communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> Seal(absl::string_view plaintext, absl::string_view associated_data);
  ~RecipientResponseContext();

 private:
  std::unique_ptr<EVP_AEAD_CTX> aead_response_context_;
  std::vector<uint8_t> response_nonce_;
};

// Holds all necessary recipient contexts.
struct RecipientContext {
  std::unique_ptr<RecipientRequestContext> recipient_request_context;
  std::unique_ptr<RecipientResponseContext> recipient_response_context;
};

// Sets up an HPKE recipient by creating a recipient context.
// Returns a tuple with a recipient request and recipient response contexts.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
absl::StatusOr<RecipientContext> SetupBaseRecipient(
    absl::string_view serialized_encapsulated_public_key, KeyPair recipient_key_pair,
    absl::string_view info);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_HPKE_RECIPIENT_CONTEXT_H_

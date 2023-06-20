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

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Helpful struct for keeping track of key information returned from the BoringSSL HPKE library.
struct KeyInfo {
  size_t key_size;
  std::vector<uint8_t> key_bytes;
};

// Context for generating encrypted requests to the recipient.
class SenderRequestContext {
 public:
  SenderRequestContext(std::unique_ptr<EVP_HPKE_CTX> hpke_context)
      : hpke_context_(std::move(hpke_context)){};

  // Encrypts message with associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> Seal(absl::string_view plaintext, absl::string_view associated_data);
  ~SenderRequestContext();

 private:
  std::unique_ptr<EVP_HPKE_CTX> hpke_context_;
};

// Context for decrypting encrypted responses from the recipient. This is based on bi-directional
// encryption using AEAD.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
class SenderResponseContext {
 public:
  SenderResponseContext(std::unique_ptr<EVP_AEAD_CTX> aead_response_context,
                        std::vector<uint8_t> response_nonce)
      : aead_response_context_(std::move(aead_response_context)), response_nonce_(response_nonce){};
  // Decrypts response message and validates associated data using AEAD as part of
  // bidirectional communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> Open(absl::string_view ciphertext, absl::string_view associated_data);
  ~SenderResponseContext();

 private:
  std::unique_ptr<EVP_AEAD_CTX> aead_response_context_;
  std::vector<uint8_t> response_nonce_;
};

// Holds all necessary sender contexts and the encapsulated public key.
struct SenderContext {
  std::vector<uint8_t> encap_public_key;
  std::unique_ptr<SenderRequestContext> sender_request_context;
  std::unique_ptr<SenderResponseContext> sender_response_context;
};

// Sets up an HPKE sender by generating an ephemeral keypair (and serializing the corresponding
// public key) and creating a sender context.
// Returns the encapsulated public key, sender request and sender response contexts.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
//
// Encapsulated public key is represented as a NIST P-256 SEC1 encoded point public key.
// <https://secg.org/sec1-v2.pdf>
absl::StatusOr<SenderContext> SetupBaseSender(absl::string_view serialized_recipient_public_key,
                                              absl::string_view info);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_HPKE_SENDER_CONTEXT_H_
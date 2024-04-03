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

#ifndef CC_CRYPTO_CLIENT_ENCRYPTOR_H_
#define CC_CRYPTO_CLIENT_ENCRYPTOR_H_

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/sender_context.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::crypto {

// Encryptor class for encrypting client requests that will be sent to the
// server and decrypting server responses that are received by the client. Each
// Encryptor corresponds to a single crypto session between the client and the
// server.
//
// Sequence numbers for requests and responses are incremented separately,
// meaning that there could be multiple responses per request and multiple
// requests per response.
class ClientEncryptor {
 public:
  // Creates a new instance of [`ClientEncryptor`].
  // The corresponding encryption and decryption keys are generated using the
  // server public key with Hybrid Public Key Encryption (HPKE).
  // <https://www.rfc-editor.org/rfc/rfc9180.html>
  //
  // `serialized_server_public_key` must be a NIST P-256 SEC1 encoded point
  // public key. <https://secg.org/sec1-v2.pdf>
  static absl::StatusOr<std::unique_ptr<ClientEncryptor>> Create(
      absl::string_view serialized_server_public_key);

  // Constructor for initializing all private variables of the class.
  explicit ClientEncryptor(std::unique_ptr<SenderContext> sender_context)
      : serialized_encapsulated_public_key_has_been_sent_(false),
        sender_context_(std::move(sender_context)){};

  // Encrypts `plaintext` and authenticates `associated_data` using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // Returns an [`oak.crypto.EncryptedRequest`] proto message.
  absl::StatusOr<::oak::crypto::v1::EncryptedRequest> Encrypt(
      absl::string_view plaintext, absl::string_view associated_data);

  // Decrypts a [`EncryptedResponse`] proto message using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // Returns a response message plaintext and associated data.
  absl::StatusOr<DecryptionResult> Decrypt(
      oak::crypto::v1::EncryptedResponse encrypted_response);

 private:
  // Encapsulated public key needed to establish a symmetric session key.
  // Only sent in the initial request message of the session.
  bool serialized_encapsulated_public_key_has_been_sent_;
  std::unique_ptr<SenderContext> sender_context_;
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_CLIENT_ENCRYPTOR_H_

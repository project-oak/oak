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

#ifndef CC_CRYPTO_ENCRYPTOR_H_
#define CC_CRYPTO_ENCRYPTOR_H_

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke.h"

namespace oak::crypto {

// Info string used by Hybrid Public Key Encryption.
constexpr absl::string_view OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1";

// Encryptor class for encrypting client requests that will be sent to the server and decrypting
// server responses that are received by the client. Each Encryptor object corresponds to a
// single crypto session between the client and the server.
//
// Sequence numbers for requests and responses are incremented separately, meaning that there could
// be multiple responses per request and multiple requests per response.
class ClientEncryptor {
 public:
  // `serialized_server_public_key` must be a NIST P-256 SEC1 encoded point public key.
  // <https://secg.org/sec1-v2.pdf>
  static absl::StatusOr<std::unique_ptr<ClientEncryptor>> Create(
      absl::string_view serialized_server_public_key);

  // Constructor for initializing all private variables of the class.
  ClientEncryptor(ClientHPKEConfig& client_hpke_config)
      : serialized_encapsulated_public_key_(std::move(client_hpke_config.encap_public_key)),
        sender_request_context_(std::move(client_hpke_config.sender_request_context)),
        sender_response_context_(std::move(client_hpke_config.sender_response_context)){};

  // Encrypts `plaintext` and authenticates `associated_data` using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // Returns a serialized [`oak.crypto.EncryptedRequest`] message.
  // TODO(#3843): Return unserialized proto messages once we have Java encryption without JNI.
  absl::StatusOr<std::string> Encrypt(absl::string_view plaintext,
                                      absl::string_view associated_data);

  // Decrypts a [`EncryptedResponse`] proto message using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // `encrypted_response` must be a serialized [`oak.crypto.EncryptedResponse`] message.
  // Returns a response message plaintext.
  // TODO(#3843): Accept unserialized proto messages once we have Java encryption without JNI.
  // std::tuple<std::string, std::string> Decrypt(absl::string_view encrypted_response);
  absl::StatusOr<std::string> Decrypt(std::string encrypted_response);

 private:
  // Encapsulated public key needed to establish a symmetric session key.
  // Only sent in the initial request message of the session.
  std::unique_ptr<KeyInfo> serialized_encapsulated_public_key_;
  std::unique_ptr<SenderRequestContext> sender_request_context_;
  std::unique_ptr<SenderResponseContext> sender_response_context_;
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_ENCRYPTOR_H_

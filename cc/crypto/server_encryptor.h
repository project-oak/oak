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

#ifndef CC_CRYPTO_SERVER_ENCRYPTOR_H_
#define CC_CRYPTO_SERVER_ENCRYPTOR_H_

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/encryption_key_provider.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "oak_crypto/proto/v1/crypto.pb.h"

namespace oak::crypto {

// Encryptor class for decrypting client requests that are received by the server and encrypting
// server responses that will be sent back to the client. Each Encryptor corresponds to a single
// crypto session between the client and the server.
//
// Sequence numbers for requests and responses are incremented separately, meaning that there could
// be multiple responses per request and multiple requests per response.
class ServerEncryptor {
 public:
  ServerEncryptor(std::shared_ptr<RecipientContextGenerator> recipient_context_generator)
      : recipient_context_generator_(recipient_context_generator),
        recipient_request_context_(nullptr),
        recipient_response_context_(nullptr){};

  // Decrypts a [`EncryptedRequest`] proto message using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // `encrypted_request` must be a serialized [`oak.crypto.EncryptedRequest`] message.
  // Returns a response message plaintext and associated data.
  // TODO(#3843): Accept unserialized proto messages once we have Java encryption without JNI.
  absl::StatusOr<DecryptionResult> Decrypt(absl::string_view encrypted_request);

  // Encrypts `plaintext` and authenticates `associated_data` using AEAD.
  // <https://datatracker.ietf.org/doc/html/rfc5116>
  //
  // Returns a serialized [`oak.crypto.EncryptedResponse`] message.
  // TODO(#3843): Return unserialized proto messages once we have Java encryption without JNI.
  absl::StatusOr<std::string> Encrypt(absl::string_view plaintext,
                                      absl::string_view associated_data);

 private:
  std::shared_ptr<RecipientContextGenerator> recipient_context_generator_;
  std::unique_ptr<RecipientRequestContext> recipient_request_context_;
  std::unique_ptr<RecipientResponseContext> recipient_response_context_;

  absl::Status InitializeRecipientContexts(const oak::crypto::v1::EncryptedRequest& request);
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_SERVER_ENCRYPTOR_H_

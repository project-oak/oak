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

#include "cc/crypto/client_encryptor.h"

#include "absl/status/statusor.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/sender_context.h"
#include "oak_crypto/proto/v1/crypto.pb.h"

namespace oak::crypto {

namespace {
using oak::crypto::v1::EncryptedRequest;
using oak::crypto::v1::EncryptedResponse;
}  // namespace

absl::StatusOr<std::unique_ptr<ClientEncryptor>> ClientEncryptor::Create(
    absl::string_view serialized_server_public_key) {
  absl::StatusOr<SenderContext> setup_base_sender_result =
      SetupBaseSender(serialized_server_public_key, OAK_HPKE_INFO);
  if (!setup_base_sender_result.ok()) {
    return setup_base_sender_result.status();
  }
  SenderContext sender_context = std::move(*setup_base_sender_result);
  return std::make_unique<ClientEncryptor>(ClientEncryptor(sender_context));
}

absl::StatusOr<std::string> ClientEncryptor::Encrypt(absl::string_view plaintext,
                                                     absl::string_view associated_data) {
  // Encrypt request.
  absl::StatusOr<std::string> seal_result =
      sender_request_context_->Seal(plaintext, associated_data);
  if (!seal_result.ok()) {
    return seal_result.status();
  }
  std::string ciphertext = std::move(*seal_result);

  // Create request message.
  EncryptedRequest request;
  *request.mutable_encrypted_message()->mutable_ciphertext() = ciphertext;
  *request.mutable_encrypted_message()->mutable_associated_data() = associated_data;

  // Encapsulated public key is only sent in the initial request message of the session.
  if (!serialized_encapsulated_public_key_.empty()) {
    *request.mutable_serialized_encapsulated_public_key() = serialized_encapsulated_public_key_;
    serialized_encapsulated_public_key_ = "";
  }

  // Serialize request.
  std::string serialized_request;
  if (!request.SerializeToString(&serialized_request)) {
    return absl::InternalError("couldn't serialize request");
  }
  return serialized_request;
}

absl::StatusOr<DecryptionResult> ClientEncryptor::Decrypt(absl::string_view encrypted_response) {
  // Deserialize response.
  EncryptedResponse response;
  if (!response.ParseFromString(encrypted_response)) {
    return absl::InvalidArgumentError("couldn't deserialize response");
  }

  // Decrypt response.
  absl::StatusOr<std::string> open_result = sender_response_context_->Open(
      response.encrypted_message().ciphertext(), response.encrypted_message().associated_data());
  if (!open_result.ok()) {
    return open_result.status();
  }
  std::string plaintext = std::move(*open_result);

  return DecryptionResult{plaintext, response.encrypted_message().associated_data()};
}

}  // namespace oak::crypto

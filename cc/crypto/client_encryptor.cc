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

#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/sender_context.h"
#include "oak_crypto/proto/v1/crypto.pb.h"

namespace oak::crypto {

namespace {
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
}  // namespace

absl::StatusOr<std::unique_ptr<ClientEncryptor>> ClientEncryptor::Create(
    absl::string_view serialized_server_public_key) {
  absl::StatusOr<std::unique_ptr<SenderContext>> sender_context =
      SetupBaseSender(serialized_server_public_key, kOakHPKEInfo);
  if (!sender_context.ok()) {
    return sender_context.status();
  }
  return std::make_unique<ClientEncryptor>(std::move(*sender_context));
}

absl::StatusOr<std::string> ClientEncryptor::Encrypt(absl::string_view plaintext,
                                                     absl::string_view associated_data) {
  // Encrypt request.
  absl::StatusOr<std::string> ciphertext = sender_context_->Seal(plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }

  // Create request message.
  EncryptedRequest request;
  *request.mutable_encrypted_message()->mutable_ciphertext() = *ciphertext;
  *request.mutable_encrypted_message()->mutable_associated_data() = associated_data;

  // Encapsulated public key is only sent in the initial request message of the session.
  if (!serialized_encapsulated_public_key_has_been_sent_) {
    *request.mutable_serialized_encapsulated_public_key() =
        sender_context_->GetSerializedEncapsulatedPublicKey();
    serialized_encapsulated_public_key_has_been_sent_ = true;
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
  absl::StatusOr<std::string> plaintext = sender_context_->Open(
      response.encrypted_message().ciphertext(), response.encrypted_message().associated_data());
  if (!plaintext.ok()) {
    return plaintext.status();
  }

  return DecryptionResult{*plaintext, response.encrypted_message().associated_data()};
}

}  // namespace oak::crypto

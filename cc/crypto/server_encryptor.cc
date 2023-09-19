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

#include "cc/crypto/server_encryptor.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "oak_crypto/proto/v1/crypto.pb.h"

namespace oak::crypto {

namespace {
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
}  // namespace

absl::StatusOr<DecryptionResult> ServerEncryptor::Decrypt(absl::string_view encrypted_request) {
  // Deserialize request.
  EncryptedRequest request;
  if (!request.ParseFromString(encrypted_request)) {
    return absl::InvalidArgumentError("couldn't deserialize request");
  }

  // Get recipient context.
  if (!recipient_request_context_) {
    absl::Status status = InitializeRecipientContexts(request);
    if (!status.ok()) {
      return status;
    }
  }

  // Decrypt request.
  absl::StatusOr<std::string> plaintext = recipient_request_context_->Open(
      request.encrypted_message().ciphertext(), request.encrypted_message().associated_data());
  if (!plaintext.ok()) {
    return plaintext.status();
  }

  return DecryptionResult{*plaintext, request.encrypted_message().associated_data()};
}

absl::StatusOr<std::string> ServerEncryptor::Encrypt(absl::string_view plaintext,
                                                     absl::string_view associated_data) {
  // Get recipient context.
  if (!recipient_response_context_) {
    return absl::InternalError("server encryptor is not initialized");
  }

  // Encrypt response.
  absl::StatusOr<std::string> ciphertext =
      recipient_response_context_->Seal(plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }

  // Create response message.
  EncryptedResponse response;
  *response.mutable_encrypted_message()->mutable_ciphertext() = *ciphertext;
  *response.mutable_encrypted_message()->mutable_associated_data() = associated_data;

  // Serialize response.
  std::string serialized_response;
  if (!response.SerializeToString(&serialized_response)) {
    return absl::InternalError("couldn't serialize response");
  }
  return serialized_response;
}

absl::Status ServerEncryptor::InitializeRecipientContexts(const EncryptedRequest& request) {
  // Get serialized encapsulated public key.
  if (!request.has_serialized_encapsulated_public_key()) {
    return absl::InvalidArgumentError(
        "serialized encapsulated public key is not present in the initial request message");
  }
  std::string serialized_encapsulated_public_key = request.serialized_encapsulated_public_key();

  // Create recipient contexts.
  absl::StatusOr<RecipientContext> recipient_context =
      recipient_context_generator_.GenerateRecipientContext(serialized_encapsulated_public_key);
  if (!recipient_context.ok()) {
    return recipient_context.status();
  }
  recipient_request_context_ = std::move(recipient_context->recipient_request_context);
  recipient_response_context_ = std::move(recipient_context->recipient_response_context);

  return absl::OkStatus();
}

}  // namespace oak::crypto

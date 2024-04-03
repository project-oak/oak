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

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/hpke/utils.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::crypto {

namespace {
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
}  // namespace

absl::StatusOr<DecryptionResult> ServerEncryptor::Decrypt(
    EncryptedRequest encrypted_request) {
  // Get recipient context.
  if (!recipient_context_) {
    absl::Status status = InitializeRecipientContexts(encrypted_request);
    if (!status.ok()) {
      return status;
    }
  }

  // Decrypt request.
  const std::vector<uint8_t> nonce(
      encrypted_request.encrypted_message().nonce().begin(),
      encrypted_request.encrypted_message().nonce().end());
  absl::StatusOr<std::string> plaintext = recipient_context_->Open(
      nonce, encrypted_request.encrypted_message().ciphertext(),
      encrypted_request.encrypted_message().associated_data());
  if (!plaintext.ok()) {
    return plaintext.status();
  }

  return DecryptionResult{
      *plaintext, encrypted_request.encrypted_message().associated_data()};
}

absl::StatusOr<EncryptedResponse> ServerEncryptor::Encrypt(
    absl::string_view plaintext, absl::string_view associated_data) {
  // Get recipient context.
  if (!recipient_context_) {
    return absl::InternalError("server encryptor is not initialized");
  }

  // Encrypt response.
  absl::StatusOr<const std::vector<uint8_t>> nonce = GenerateRandomNonce();
  if (!nonce.ok()) {
    return nonce.status();
  }
  absl::StatusOr<std::string> ciphertext =
      recipient_context_->Seal(*nonce, plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }

  // Create response message.
  EncryptedResponse encrypted_response;
  *encrypted_response.mutable_encrypted_message()->mutable_nonce() =
      std::string(nonce->begin(), nonce->end());
  *encrypted_response.mutable_encrypted_message()->mutable_ciphertext() =
      *ciphertext;
  *encrypted_response.mutable_encrypted_message()->mutable_associated_data() =
      associated_data;

  return encrypted_response;
}

absl::Status ServerEncryptor::InitializeRecipientContexts(
    const EncryptedRequest& request) {
  // Get serialized encapsulated public key.
  if (!request.has_serialized_encapsulated_public_key()) {
    return absl::InvalidArgumentError(
        "serialized encapsulated public key is not present in the initial "
        "request message");
  }
  std::string serialized_encapsulated_public_key =
      request.serialized_encapsulated_public_key();

  // Create recipient contexts.
  absl::StatusOr<std::unique_ptr<RecipientContext>> recipient_context =
      encryption_key_handle_.GenerateRecipientContext(
          serialized_encapsulated_public_key);
  if (!recipient_context.ok()) {
    return recipient_context.status();
  }
  recipient_context_ = std::move(*recipient_context);

  return absl::OkStatus();
}

}  // namespace oak::crypto

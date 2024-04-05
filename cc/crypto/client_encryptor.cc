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

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/sender_context.h"
#include "cc/crypto/hpke/utils.h"
#include "proto/crypto/crypto.pb.h"

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

absl::StatusOr<EncryptedRequest> ClientEncryptor::Encrypt(
    absl::string_view plaintext, absl::string_view associated_data) {
  // Encrypt request.
  absl::StatusOr<const std::vector<uint8_t>> nonce = GenerateRandomNonce();
  if (!nonce.ok()) {
    return nonce.status();
  }
  absl::StatusOr<std::string> ciphertext =
      sender_context_->Seal(*nonce, plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }

  // Create request message.
  EncryptedRequest encrypted_request;
  *encrypted_request.mutable_encrypted_message()->mutable_nonce() =
      std::string(nonce->begin(), nonce->end());
  *encrypted_request.mutable_encrypted_message()->mutable_ciphertext() =
      *ciphertext;
  *encrypted_request.mutable_encrypted_message()->mutable_associated_data() =
      associated_data;

  // Encapsulated public key is only sent in the initial request message of the
  // session.
  if (!serialized_encapsulated_public_key_has_been_sent_) {
    *encrypted_request.mutable_serialized_encapsulated_public_key() =
        sender_context_->GetSerializedEncapsulatedPublicKey();
    serialized_encapsulated_public_key_has_been_sent_ = true;
  }

  return encrypted_request;
}

absl::StatusOr<DecryptionResult> ClientEncryptor::Decrypt(
    EncryptedResponse encrypted_response) {
  // Decrypt response.
  const std::vector<uint8_t> nonce(
      encrypted_response.encrypted_message().nonce().begin(),
      encrypted_response.encrypted_message().nonce().end());
  absl::StatusOr<std::string> plaintext = sender_context_->Open(
      nonce, encrypted_response.encrypted_message().ciphertext(),
      encrypted_response.encrypted_message().associated_data());
  if (!plaintext.ok()) {
    return plaintext.status();
  }

  return DecryptionResult{
      *plaintext, encrypted_response.encrypted_message().associated_data()};
}

}  // namespace oak::crypto

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

#include "cc/crypto/encryptor.h"

#include "absl/status/statusor.h"
#include "cc/crypto/hpke/hpke.h"
#include "oak_crypto/proto/v1/crypto.pb.h"

namespace oak::crypto {
namespace {

using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;

// Generates a string form of a KeyInfo struct with length key_size.
std::string KeyInfoToString(KeyInfo key_info) {
  size_t key_size = key_info.key_size;
  key_info.key_bytes.resize(key_size);
  std::string key(key_info.key_bytes.begin(), key_info.key_bytes.end());
  return key;
}
}  // namespace

absl::StatusOr<std::unique_ptr<ClientEncryptor>> ClientEncryptor::Create(
    absl::string_view serialized_server_public_key) {
  absl::StatusOr<ClientHPKEConfig> client_setup =
      SetUpBaseSender(serialized_server_public_key, OAK_HPKE_INFO);
  if (!client_setup.ok()) {
    return client_setup.status();
  }
  std::unique_ptr<ClientEncryptor> client_encryptor =
      std::make_unique<ClientEncryptor>(*client_setup);
  // Pass ownership of the pointer to the caller.
  return std::move(client_encryptor);
}

absl::StatusOr<std::string> ClientEncryptor::Encrypt(absl::string_view plaintext,
                                                     absl::string_view associated_data) {
  EncryptedRequest encrypted_request_proto;
  auto serialized_encrypted_message = sender_request_context_->Seal(plaintext, associated_data);
  if (!serialized_encrypted_message.ok()) {
    return serialized_encrypted_message.status();
  }
  *encrypted_request_proto.mutable_encrypted_message()->mutable_ciphertext() =
      *serialized_encrypted_message;
  KeyInfo serialized_encapsulated_public_key = *serialized_encapsulated_public_key_.get();

  *encrypted_request_proto.mutable_serialized_encapsulated_public_key() =
      KeyInfoToString(serialized_encapsulated_public_key);

  std::string serialized_output;
  if (encrypted_request_proto.SerializeToString(&serialized_output)) {
    return absl::AbortedError("Failed to serialize EncrytpedRequest proto.");
  }
  return serialized_output;
}

absl::StatusOr<std::string> ClientEncryptor::Decrypt(std::string encrypted_response) {
  EncryptedResponse encrypted_response_proto;
  if (!encrypted_response_proto.ParseFromString(encrypted_response)) {
    return absl::AbortedError("Unable to parse encrypted response to proto format.");
  }
  std::string ciphertext = encrypted_response_proto.encrypted_message().ciphertext();
  std::string associated_data = encrypted_response_proto.encrypted_message().associated_data();
  return sender_response_context_->Open(ciphertext, associated_data);
}
}  // namespace oak::crypto

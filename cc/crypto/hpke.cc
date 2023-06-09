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

#include "hpke.h"

#include <memory>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"

namespace oak::crypto {

namespace {
constexpr size_t kAeadAlgorithmKeySizeBytes = 32;
constexpr size_t kAeadNonceSizeBytes = 12;

// Converts a string view object to a vector of bytes.
std::vector<uint8_t> StringViewToBytes(absl::string_view str_view) {
  std::vector<uint8_t> byte_array;
  for (char character : str_view) {
    byte_array.push_back(character);
  }
  return byte_array;
}
}  // namespace

absl::StatusOr<std::string> SenderRequestContext::Seal(absl::string_view plaintext,
                                                       absl::string_view associated_data) {
  std::vector<uint8_t> plaintext_bytes = StringViewToBytes(plaintext);
  std::vector<uint8_t> associated_data_bytes = StringViewToBytes(associated_data);
  size_t max_out_len = EVP_HPKE_CTX_max_overhead(hpke_context_.get()) + plaintext_bytes.size();

  std::vector<uint8_t> encrypted_message(max_out_len);
  size_t encrypted_message_len;
  if (!EVP_HPKE_CTX_seal(
          /* ctx= */ hpke_context_.get(),
          /* out= */ encrypted_message.data(),
          /* out_len= */ &encrypted_message_len,
          /* max_out_len= */ max_out_len,
          /* in= */ plaintext_bytes.data(),
          /* in_len= */ plaintext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Failed to seal request");
  }
  encrypted_message.resize(encrypted_message_len);

  std::string serialized_encrypted_message(encrypted_message.begin(), encrypted_message.end());
  return serialized_encrypted_message;
}

SenderRequestContext::~SenderRequestContext() { EVP_HPKE_CTX_cleanup(hpke_context_.release()); }

absl::StatusOr<std::string> SenderResponseContext::Open(absl::string_view ciphertext,
                                                        absl::string_view associated_data) {
  std::vector<uint8_t> ciphertext_bytes = StringViewToBytes(ciphertext);
  std::vector<uint8_t> associated_data_bytes = StringViewToBytes(associated_data);

  // The plaintext should not be longer than the ciphertext.
  std::vector<uint8_t> plaintext_bytes(ciphertext_bytes.size());
  size_t plaintext_bytes_size;
  if (!EVP_AEAD_CTX_open(
          /* ctx= */ aead_response_context_.get(),
          /* out= */ plaintext_bytes.data(),
          /* out_len= */ &plaintext_bytes_size,
          /* max_out_len= */ ciphertext_bytes.size(),
          /* nonce= */ response_nonce_->key_bytes.data(),
          /* nonce_len= */ response_nonce_->key_size,
          /* in= */ ciphertext_bytes.data(),
          /* in_len= */ ciphertext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Unable to decrypt response message");
  }
  plaintext_bytes.resize(plaintext_bytes_size);
  std::string plaintext(plaintext_bytes.begin(), plaintext_bytes.end());
  return plaintext;
}

absl::StatusOr<ClientHPKEConfig> SetUpBaseSender(absl::string_view serialized_recipient_public_key,
                                                 absl::string_view info) {
  ClientHPKEConfig client_hpke_config;

  // First collect encapsulated public key information and sender request context.
  std::unique_ptr<KeyInfo>& encap_public_key = client_hpke_config.encap_public_key;
  encap_public_key = std::unique_ptr<KeyInfo>(new KeyInfo());
  encap_public_key->key_bytes.reserve(EVP_HPKE_MAX_ENC_LENGTH);

  std::vector<uint8_t> recipient_public_key_bytes =
      StringViewToBytes(serialized_recipient_public_key);
  std::vector<uint8_t> info_bytes = StringViewToBytes(info);

  std::unique_ptr<EVP_HPKE_CTX> hpke_sender_context(EVP_HPKE_CTX_new());
  if (hpke_sender_context == nullptr) {
    return absl::AbortedError("Unable to generate HPKE sender context");
  }
  // Create sender context.
  if (!EVP_HPKE_CTX_setup_sender(
          /* ctx= */ hpke_sender_context.get(),
          /* out_enc= */ encap_public_key->key_bytes.data(),
          /* out_enc_len= */ &encap_public_key->key_size,
          /* max_enc= */ EVP_HPKE_MAX_ENC_LENGTH,
          /* kem= */ EVP_hpke_x25519_hkdf_sha256(),
          /* kdf= */ EVP_hpke_hkdf_sha256(),
          /* aead= */ EVP_hpke_aes_256_gcm(),
          /* peer_public_key= */ recipient_public_key_bytes.data(),
          /* peer_public_key_len= */ recipient_public_key_bytes.size(),
          /* info= */ info_bytes.data(),
          /* info_len= */ info_bytes.size())) {
    return absl::AbortedError("Unable to setup sender context.");
  }
  // Generate sender response context from hpke context.
  std::unique_ptr<SenderRequestContext>& sender_request_context =
      client_hpke_config.sender_request_context;
  sender_request_context = std::unique_ptr<SenderRequestContext>(
      new SenderRequestContext(std::move(hpke_sender_context)));

  // Now configure sender response context.
  // Generate response key for the response context.
  KeyInfo response_key;
  response_key.key_bytes.reserve(kAeadAlgorithmKeySizeBytes);
  response_key.key_size = kAeadAlgorithmKeySizeBytes;
  std::string key_context_string = "response_key";
  std::vector<uint8_t> key_context_bytes(key_context_string.begin(), key_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_sender_context.get(),
          /* out= */ response_key.key_bytes.data(),
          /* secret_len= */ kAeadAlgorithmKeySizeBytes,
          /* context= */ key_context_bytes.data(),
          /* context_len= */ key_context_bytes.size())) {
    return absl::AbortedError("Unable to export client response key.");
  }

  std::unique_ptr<EVP_AEAD_CTX> aead_response_context(EVP_AEAD_CTX_new(
      /* aead= */ EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()),
      /* key= */ response_key.key_bytes.data(),
      /* key_len= */ response_key.key_size,
      /* tag_len= */ 0));

  if (aead_response_context == nullptr) {
    return absl::AbortedError("Unable to generate AEAD response context.");
  }

  // Generate a nonce for the response context.
  std::unique_ptr<KeyInfo> response_nonce = std::unique_ptr<KeyInfo>(new KeyInfo());
  response_nonce->key_bytes.reserve(kAeadNonceSizeBytes);
  response_nonce->key_size = kAeadNonceSizeBytes;
  std::string nonce_context_string = "response_nonce";
  std::vector<uint8_t> nonce_context_bytes(nonce_context_string.begin(),
                                           nonce_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_sender_context.get(),
          /* out= */ response_nonce->key_bytes.data(),
          /* secret_len= */ kAeadNonceSizeBytes,
          /* context= */ nonce_context_bytes.data(),
          /* context_len= */ nonce_context_bytes.size())) {
    return absl::AbortedError("Unable to export client response nonce.");
  }
  std::unique_ptr<SenderResponseContext>& sender_response_context =
      client_hpke_config.sender_response_context;
  sender_response_context = std::unique_ptr<SenderResponseContext>(
      new SenderResponseContext(std::move(aead_response_context), std::move(response_nonce)));

  return client_hpke_config;
}
}  // namespace oak::crypto

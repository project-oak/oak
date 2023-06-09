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
#include "util.h"

namespace oak::crypto {

constexpr size_t kAeadAlgorithmKeySizeBytes = 32;
constexpr size_t kAeadNonceSizeBytes = 12;

absl::StatusOr<std::string> SenderRequestContext::Seal(absl::string_view plaintext,
                                                       absl::string_view associated_data) {
  return "";
}

absl::StatusOr<std::string> SenderResponseContext::Open(absl::string_view ciphertext,
                                                        absl::string_view associated_data) {
  return "";
}

absl::StatusOr<ClientHPKEConfig> SetUpBaseSender(absl::string_view serialized_recipient_public_key,
                                                 absl::string_view info) {
  ClientHPKEConfig client_hpke_context;

  // First collect encapsulated public key information and sender request context.
  std::unique_ptr<EVP_HPKE_CTX> hpke_sender_context(EVP_HPKE_CTX_new());
  std::vector<uint8_t> encap_shared_secret(EVP_HPKE_MAX_ENC_LENGTH);
  size_t encap_shared_secret_len;

  std::vector<uint8_t> recipient_public_key_bytes =
      StringViewToBytes(serialized_recipient_public_key);
  std::vector<uint8_t> info_bytes = StringViewToBytes(info);

  // Create sender context.
  if (!EVP_HPKE_CTX_setup_sender(
          /* ctx= */ hpke_sender_context.get(),
          /* out_enc= */ encap_shared_secret.data(),
          /* out_enc_len= */ &encap_shared_secret_len,
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
      client_hpke_context.sender_request_context;
  sender_request_context = std::unique_ptr<SenderRequestContext>(
      new SenderRequestContext(std::move(hpke_sender_context)));

  // Record encapsulated public key information.
  std::unique_ptr<KeyInfo>& encap_public_key_info = client_hpke_context.encap_public_key_info;
  encap_public_key_info = std::unique_ptr<KeyInfo>(new KeyInfo());
  encap_public_key_info->key_size = encap_shared_secret_len;
  encap_public_key_info->key_bytes = encap_shared_secret;

  // Now generate response key and response nonce for sender response context.
  std::vector<uint8_t> response_key(kAeadAlgorithmKeySizeBytes);
  std::string key_context_string = "response_key";
  std::vector<uint8_t> key_context_bytes(key_context_string.begin(), key_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_sender_context.get(),
          /* out= */ response_key.data(),
          /* secret_len= */ kAeadAlgorithmKeySizeBytes,
          /* context= */ key_context_bytes.data(),
          /* context_len= */ key_context_bytes.size())) {
    return absl::AbortedError("Unable to export client response key.");
  }

  // Generate a nonce for the response.
  std::vector<uint8_t> response_nonce(kAeadNonceSizeBytes);
  std::string nonce_context_string = "response_nonce";
  std::vector<uint8_t> nonce_context_bytes(nonce_context_string.begin(),
                                           nonce_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_sender_context.get(),
          /* out= */ response_nonce.data(),
          /* secret_len= */ kAeadNonceSizeBytes,
          /* context= */ nonce_context_bytes.data(),
          /* context_len= */ nonce_context_bytes.size())) {
    return absl::AbortedError("Unable to export client response nonce.");
  }

  // Generate and return the client HPKE contexts.

  std::unique_ptr<SenderResponseContext>& sender_response_context =
      client_hpke_context.sender_response_context;
  sender_response_context = new SenderResponseContext(std::move());

  return client_hpke_context;
}
}  // namespace oak::crypto

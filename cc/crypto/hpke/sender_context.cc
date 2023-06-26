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

#include "cc/crypto/hpke/sender_context.h"

#include <memory>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/utils.h"
#include "openssl/aead.h"
#include "openssl/hpke.h"

namespace oak::crypto {

absl::StatusOr<std::string> SenderRequestContext::Seal(absl::string_view plaintext,
                                                       absl::string_view associated_data) {
  std::vector<uint8_t> plaintext_bytes(plaintext.begin(), plaintext.end());
  std::vector<uint8_t> associated_data_bytes(associated_data.begin(), associated_data.end());
  size_t max_out_len = EVP_HPKE_CTX_max_overhead(hpke_context_.get()) + plaintext_bytes.size();

  std::vector<uint8_t> ciphertext_bytes(max_out_len);
  size_t ciphertext_bytes_len;
  if (!EVP_HPKE_CTX_seal(
          /* ctx= */ hpke_context_.get(),
          /* out= */ ciphertext_bytes.data(),
          /* out_len= */ &ciphertext_bytes_len,
          /* max_out_len= */ max_out_len,
          /* in= */ plaintext_bytes.data(),
          /* in_len= */ plaintext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Failed to seal request");
  }
  ciphertext_bytes.resize(ciphertext_bytes_len);

  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());
  return ciphertext;
}

SenderRequestContext::~SenderRequestContext() { EVP_HPKE_CTX_free(hpke_context_.release()); }

absl::StatusOr<std::string> SenderResponseContext::Open(absl::string_view ciphertext,
                                                        absl::string_view associated_data) {
  std::vector<uint8_t> ciphertext_bytes(ciphertext.begin(), ciphertext.end());
  if (ciphertext_bytes.empty()) {
    return absl::InvalidArgumentError("No ciphertext was provided.");
  }
  std::vector<uint8_t> associated_data_bytes(associated_data.begin(), associated_data.end());

  // The plaintext should not be longer than the ciphertext.
  std::vector<uint8_t> plaintext_bytes(ciphertext_bytes.size());
  size_t plaintext_bytes_size;

  if (!EVP_AEAD_CTX_open(
          /* ctx= */ aead_response_context_.get(),
          /* out= */ plaintext_bytes.data(),
          /* out_len= */ &plaintext_bytes_size,
          /* max_out_len= */ ciphertext_bytes.size(),
          /* nonce= */ response_nonce_.data(),
          /* nonce_len= */ response_nonce_.size(),
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

SenderResponseContext::~SenderResponseContext() {
  EVP_AEAD_CTX_free(aead_response_context_.release());
}

absl::StatusOr<SenderContext> SetupBaseSender(absl::string_view serialized_recipient_public_key,
                                              absl::string_view info) {
  SenderContext sender_hpke_info;

  // First collect encapsulated public key information and sender request context.
  KeyInfo encap_public_key_info;
  encap_public_key_info.key_bytes = std::vector<uint8_t>(EVP_HPKE_MAX_ENC_LENGTH);

  std::vector<uint8_t> recipient_public_key_bytes(serialized_recipient_public_key.begin(),
                                                  serialized_recipient_public_key.end());

  if (recipient_public_key_bytes.empty()) {
    return absl::InvalidArgumentError("No key was provided.");
  }

  std::vector<uint8_t> info_bytes(info.begin(), info.end());

  std::unique_ptr<EVP_HPKE_CTX> hpke_sender_context(EVP_HPKE_CTX_new());
  if (hpke_sender_context == nullptr) {
    return absl::AbortedError("Unable to generate HPKE sender context");
  }

  if (!EVP_HPKE_CTX_setup_sender(
          /* ctx= */ hpke_sender_context.get(),
          /* out_enc= */ encap_public_key_info.key_bytes.data(),
          /* out_enc_len= */ &encap_public_key_info.key_size,
          /* max_enc= */ encap_public_key_info.key_bytes.size(),
          /* kem= */ EVP_hpke_x25519_hkdf_sha256(),
          /* kdf= */ EVP_hpke_hkdf_sha256(),
          /* aead= */ EVP_hpke_aes_256_gcm(),
          /* peer_public_key= */ recipient_public_key_bytes.data(),
          /* peer_public_key_len= */ recipient_public_key_bytes.size(),
          /* info= */ info_bytes.data(),
          /* info_len= */ info_bytes.size())) {
    return absl::AbortedError("Unable to setup sender context.");
  }

  SenderContext sender_context;

  encap_public_key_info.key_bytes.resize(encap_public_key_info.key_size);
  sender_context.encap_public_key = encap_public_key_info.key_bytes;

  // Now configure sender response context and nonce.
  auto aead_response_context = GetResponseContext(hpke_sender_context.get());
  if (!aead_response_context.ok()) {
    return aead_response_context.status();
  }

  auto response_nonce = GetResponseNonce(hpke_sender_context.get());
  if (!response_nonce.ok()) {
    return response_nonce.status();
  }

  // Create sender request and response contexts.
  std::unique_ptr<SenderRequestContext>& sender_request_context =
      sender_context.sender_request_context;
  sender_request_context = std::make_unique<SenderRequestContext>(std::move(hpke_sender_context));

  std::unique_ptr<SenderResponseContext>& sender_response_context =
      sender_context.sender_response_context;
  sender_response_context =
      std::make_unique<SenderResponseContext>(*std::move(aead_response_context), *response_nonce);

  return sender_context;
}
}  // namespace oak::crypto

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

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/utils.h"
#include "openssl/hpke.h"

namespace oak::crypto {

absl::StatusOr<std::string> SenderContext::Seal(
    const std::vector<uint8_t>& nonce, absl::string_view plaintext,
    absl::string_view associated_data) {
  absl::StatusOr<std::string> ciphertext =
      AeadSeal(request_aead_context_.get(), nonce, plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }
  return ciphertext;
}

absl::StatusOr<std::string> SenderContext::Open(
    const std::vector<uint8_t>& nonce, absl::string_view ciphertext,
    absl::string_view associated_data) {
  absl::StatusOr<std::string> plaintext = AeadOpen(
      response_aead_context_.get(), nonce, ciphertext, associated_data);
  if (!plaintext.ok()) {
    return plaintext.status();
  }
  return plaintext;
}

SenderContext::~SenderContext() {
  EVP_AEAD_CTX_free(request_aead_context_.release());
  EVP_AEAD_CTX_free(response_aead_context_.release());
}

absl::StatusOr<std::unique_ptr<SenderContext>> SetupBaseSender(
    absl::string_view serialized_recipient_public_key, absl::string_view info) {
  // First collect encapsulated public key information and sender request
  // context.
  KeyInfo encap_public_key_info;
  encap_public_key_info.key_bytes =
      std::vector<uint8_t>(EVP_HPKE_MAX_ENC_LENGTH);

  std::vector<uint8_t> recipient_public_key_bytes(
      serialized_recipient_public_key.begin(),
      serialized_recipient_public_key.end());

  if (recipient_public_key_bytes.empty()) {
    return absl::InvalidArgumentError("No key was provided");
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
    return absl::AbortedError("Unable to setup sender context");
  }
  encap_public_key_info.key_bytes.resize(encap_public_key_info.key_size);

  // Configure sender request context.
  // This is a deviation from the HPKE RFC, because we are deriving both session
  // request and response keys from the exporter secret, instead of having a
  // request key be directly derived from the shared secret. This is required to
  // be able to share session keys between the Kernel and the Application via
  // RPC.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  auto request_aead_context =
      GetContext(hpke_sender_context.get(), "request_key");
  if (!request_aead_context.ok()) {
    return request_aead_context.status();
  }

  // Configure sender response context.
  auto response_aead_context =
      GetContext(hpke_sender_context.get(), "response_key");
  if (!response_aead_context.ok()) {
    return response_aead_context.status();
  }

  // Create sender context.
  std::unique_ptr<SenderContext> sender_context =
      std::make_unique<SenderContext>(
          /* encapsulated_public_key= */ encap_public_key_info.key_bytes,
          /* request_aead_context= */ *std::move(request_aead_context),
          /* response_aead_context= */ *std::move(response_aead_context));

  EVP_HPKE_CTX_free(hpke_sender_context.release());
  return sender_context;
}
}  // namespace oak::crypto

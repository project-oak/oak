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

#include "cc/crypto/hpke/recipient_context.h"

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
#include "proto/crypto/crypto.pb.h"

namespace oak::crypto {

namespace {
using ::oak::crypto::v1::SessionKeys;

// Validates that the public and private key pairing is valid for HPKE. If the
// public and private keys are valid, the recipient_keys argument will be an
// initialized HPKE_KEY.
absl::Status ValidateKeys(std::vector<uint8_t>& public_key_bytes,
                          std::vector<uint8_t>& private_key_bytes,
                          std::vector<uint8_t> encap_public_key_bytes,
                          EVP_HPKE_KEY* recipient_keys) {
  if (private_key_bytes.empty()) {
    return absl::InvalidArgumentError("A private key must be provided");
  }
  if (public_key_bytes.empty()) {
    return absl::InvalidArgumentError("A public key must be provided");
  }
  if (encap_public_key_bytes.empty()) {
    return absl::InvalidArgumentError(
        "An encapsulated public key must be provided");
  }

  if (!EVP_HPKE_KEY_init(
          /* key= */ recipient_keys,
          /* kem= */ EVP_hpke_x25519_hkdf_sha256(),
          /* priv_key= */ private_key_bytes.data(),
          /* priv_key_len= */ private_key_bytes.size())) {
    return absl::AbortedError("Failed to generate HPKE keys for validation");
  }

  std::vector<uint8_t> verified_public_key_bytes(public_key_bytes.size());
  size_t verfied_public_key_size;
  if (!EVP_HPKE_KEY_public_key(
          /* key= */ recipient_keys,
          /* out= */ verified_public_key_bytes.data(),
          /* out_len= */ &verfied_public_key_size,
          /* max_out= */ verified_public_key_bytes.size())) {
    return absl::AbortedError("Failed to get public key");
  }

  if (public_key_bytes != verified_public_key_bytes) {
    return absl::InvalidArgumentError("Public key does not match private key");
  }
  return absl::OkStatus();
}
}  // namespace

absl::StatusOr<std::unique_ptr<RecipientContext>> RecipientContext::Deserialize(
    SessionKeys session_keys) {
  std::unique_ptr<EVP_AEAD_CTX> request_aead_context(EVP_AEAD_CTX_new(
      /* aead= */ EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()),
      /* key= */ (uint8_t*)session_keys.request_key().data(),
      /* key_len= */ session_keys.request_key().size(),
      /* tag_len= */ 0));
  if (request_aead_context == nullptr) {
    return absl::AbortedError("Unable to deserialize request AEAD context");
  }

  std::unique_ptr<EVP_AEAD_CTX> response_aead_context(EVP_AEAD_CTX_new(
      /* aead= */ EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()),
      /* key= */ (uint8_t*)session_keys.response_key().data(),
      /* key_len= */ session_keys.response_key().size(),
      /* tag_len= */ 0));
  if (response_aead_context == nullptr) {
    return absl::AbortedError("Unable to deserialize response AEAD context");
  }

  return std::make_unique<RecipientContext>(
      /* request_aead_context= */ std::move(request_aead_context),
      /* response_aead_context= */ std::move(response_aead_context));
}

absl::StatusOr<std::string> RecipientContext::Open(
    const std::vector<uint8_t>& nonce, absl::string_view ciphertext,
    absl::string_view associated_data) {
  absl::StatusOr<std::string> plaintext =
      AeadOpen(request_aead_context_.get(), nonce, ciphertext, associated_data);
  if (!plaintext.ok()) {
    return plaintext.status();
  }
  return plaintext;
}

absl::StatusOr<std::string> RecipientContext::Seal(
    const std::vector<uint8_t>& nonce, absl::string_view plaintext,
    absl::string_view associated_data) {
  absl::StatusOr<std::string> ciphertext =
      AeadSeal(response_aead_context_.get(), nonce, plaintext, associated_data);
  if (!ciphertext.ok()) {
    return ciphertext.status();
  }
  return ciphertext;
}

RecipientContext::~RecipientContext() {
  EVP_AEAD_CTX_free(request_aead_context_.release());
  EVP_AEAD_CTX_free(response_aead_context_.release());
}

absl::StatusOr<std::unique_ptr<RecipientContext>> SetupBaseRecipient(
    absl::string_view serialized_encapsulated_public_key,
    const KeyPair& recipient_key_pair, absl::string_view info) {
  // First verify that the supplied key pairing is valid using the BoringSSL
  // library.
  std::vector<uint8_t> private_key_bytes(recipient_key_pair.private_key.begin(),
                                         recipient_key_pair.private_key.end());
  std::vector<uint8_t> public_key_bytes(recipient_key_pair.public_key.begin(),
                                        recipient_key_pair.public_key.end());
  std::vector<uint8_t> encap_public_key_bytes(
      serialized_encapsulated_public_key.begin(),
      serialized_encapsulated_public_key.end());

  bssl::ScopedEVP_HPKE_KEY recipient_keys;

  absl::Status keys_valid_status =
      ValidateKeys(public_key_bytes, private_key_bytes, encap_public_key_bytes,
                   recipient_keys.get());
  if (!keys_valid_status.ok()) {
    return keys_valid_status;
  }
  std::vector<uint8_t> info_bytes(info.begin(), info.end());

  std::unique_ptr<EVP_HPKE_CTX> hpke_recipient_context(EVP_HPKE_CTX_new());
  if (hpke_recipient_context == nullptr) {
    return absl::AbortedError("Unable to generate HPKE recipient context");
  }

  if (!EVP_HPKE_CTX_setup_recipient(
          /* ctx= */ hpke_recipient_context.get(),
          /* key= */ recipient_keys.get(),
          /* kdf= */ EVP_hpke_hkdf_sha256(),
          /* aead= */ EVP_hpke_aes_256_gcm(),
          /* enc= */ encap_public_key_bytes.data(),
          /* enc_len= */ encap_public_key_bytes.size(),
          /* info= */ info_bytes.data(),
          /* info_len= */ info_bytes.size())) {
    return absl::AbortedError("Unable to setup recipient context");
  }

  // Configure recipient request context.
  // This is a deviation from the HPKE RFC, because we are deriving both session
  // request and response keys from the exporter secret, instead of having a
  // request key be directly derived from the shared secret. This is required to
  // be able to share session keys between the Kernel and the Application via
  // RPC.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  auto request_aead_context =
      GetContext(hpke_recipient_context.get(), "request_key");
  if (!request_aead_context.ok()) {
    return request_aead_context.status();
  }

  // Configure recipient response context.
  auto response_aead_context =
      GetContext(hpke_recipient_context.get(), "response_key");
  if (!response_aead_context.ok()) {
    return response_aead_context.status();
  }

  // Create recipient context.
  std::unique_ptr<RecipientContext> recipient_context =
      std::make_unique<RecipientContext>(
          /* request_aead_context= */ *std::move(request_aead_context),
          /* response_aead_context= */ *std::move(response_aead_context));

  EVP_HPKE_CTX_free(hpke_recipient_context.release());
  return recipient_context;
}

absl::StatusOr<KeyPair> KeyPair::Generate() {
  bssl::ScopedEVP_HPKE_KEY recipient_keys;

  if (!EVP_HPKE_KEY_generate(
          /* key= */ recipient_keys.get(),
          /* kem= */ EVP_hpke_x25519_hkdf_sha256())) {
    return absl::AbortedError("Failed to generate HPKE keys");
  }

  std::vector<uint8_t> public_key_bytes(EVP_HPKE_MAX_PUBLIC_KEY_LENGTH);
  size_t public_key_bytes_len;
  if (!EVP_HPKE_KEY_public_key(
          /* key= */ recipient_keys.get(),
          /* out= */ public_key_bytes.data(),
          /* out_len= */ &public_key_bytes_len,
          /* max_out= */ public_key_bytes.size())) {
    return absl::AbortedError("Failed to retrieve public key");
  }
  public_key_bytes.resize(public_key_bytes_len);

  std::vector<uint8_t> private_key_bytes(EVP_HPKE_MAX_PRIVATE_KEY_LENGTH);
  size_t private_key_bytes_len;
  if (!EVP_HPKE_KEY_private_key(
          /* key= */ recipient_keys.get(),
          /* out= */ private_key_bytes.data(),
          /* out_len= */ &private_key_bytes_len,
          /* max_out= */ private_key_bytes.size())) {
    return absl::AbortedError("Failed to retrieve private key");
  }
  private_key_bytes.resize(private_key_bytes_len);

  std::string public_key(public_key_bytes.begin(), public_key_bytes.end());
  std::string private_key(private_key_bytes.begin(), private_key_bytes.end());

  return KeyPair{private_key, public_key};
}

}  // namespace oak::crypto

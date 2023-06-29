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

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"

namespace oak::crypto {
namespace {
// Validates that the public and private key pairing is valid for HPKE. If the public and private
// keys are valid, the recipient_keys argument will be an initialized HPKE_KEY.
absl::Status ValidateKeys(std::vector<uint8_t>& public_key_bytes,
                          std::vector<uint8_t>& private_key_bytes,
                          std::vector<uint8_t> encap_public_key_bytes,
                          EVP_HPKE_KEY* recipient_keys) {
  if (private_key_bytes.empty()) {
    return absl::InvalidArgumentError("A private key must be provided.");
  }
  if (public_key_bytes.empty()) {
    return absl::InvalidArgumentError("A public key must be provided.");
  }
  if (encap_public_key_bytes.empty()) {
    return absl::InvalidArgumentError("An encapsulated public key must be provided.");
  }

  if (!EVP_HPKE_KEY_init(
          /* key= */ recipient_keys,
          /* kem= */ EVP_hpke_x25519_hkdf_sha256(),
          /* priv_key= */ private_key_bytes.data(),
          /* priv_key_len= */ private_key_bytes.size())) {
    return absl::AbortedError("Failed to generate HPKE keys for validation.");
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

absl::StatusOr<std::string> RecipientRequestContext::Open(absl::string_view ciphertext,
                                                          absl::string_view associated_data) {
  std::vector<uint8_t> ciphertext_bytes(ciphertext.begin(), ciphertext.end());
  std::vector<uint8_t> associated_data_bytes(associated_data.begin(), associated_data.end());

  // The plaintext should never be longer than the ciphertext.
  size_t max_out_len = ciphertext_bytes.size();
  std::vector<uint8_t> plaintext_bytes(max_out_len);
  size_t plaintext_bytes_len;
  if (!EVP_HPKE_CTX_open(
          /* ctx= */ hpke_context_.get(),
          /* out= */ plaintext_bytes.data(),
          /* out_len= */ &plaintext_bytes_len,
          /* max_out_len= */ max_out_len,
          /* in= */ ciphertext_bytes.data(),
          /* in_len= */ ciphertext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Failed to open encrypted message.");
  }
  plaintext_bytes.resize(plaintext_bytes_len);
  std::string plaintext(plaintext_bytes.begin(), plaintext_bytes.end());
  return plaintext;
}

RecipientRequestContext::~RecipientRequestContext() { EVP_HPKE_CTX_free(hpke_context_.release()); }

absl::StatusOr<std::string> RecipientResponseContext::Seal(absl::string_view plaintext,
                                                           absl::string_view associated_data) {
  std::vector<uint8_t> plaintext_bytes(plaintext.begin(), plaintext.end());
  if (plaintext_bytes.empty()) {
    return absl::InvalidArgumentError("No plaintext was provided");
  }
  std::vector<uint8_t> associated_data_bytes(associated_data.begin(), associated_data.end());
  size_t max_out_len =
      plaintext_bytes.size() + EVP_AEAD_max_overhead(EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()));

  std::vector<uint8_t> ciphertext_bytes(max_out_len);
  size_t ciphertext_bytes_len;

  /// Maximum sequence number which can fit in kAeadNonceSizeBytes bytes.
  /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  if (sequence_number_ == UINT64_MAX) {
    return absl::OutOfRangeError("Sequence number reached.");
  }
  std::vector<uint8_t> nonce = CalculateNonce(response_base_nonce_, sequence_number_);
  sequence_number_ += 1;

  if (!EVP_AEAD_CTX_seal(
          /* ctx= */ aead_response_context_.get(),
          /* out= */ ciphertext_bytes.data(),
          /* out_len= */ &ciphertext_bytes_len,
          /* max_out_len= */ ciphertext_bytes.size(),
          /* nonce= */ nonce.data(),
          /* nonce_len= */ nonce.size(),
          /* in= */ plaintext_bytes.data(),
          /* in_len= */ plaintext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Unable to seal response messge");
  }
  ciphertext_bytes.resize(ciphertext_bytes_len);
  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());
  return ciphertext;
}

RecipientResponseContext::~RecipientResponseContext() {
  EVP_AEAD_CTX_free(aead_response_context_.release());
}

absl::StatusOr<RecipientContext> SetupBaseRecipient(
    absl::string_view serialized_encapsulated_public_key, const KeyPair& recipient_key_pair,
    absl::string_view info) {
  // First verify that the supplied key pairing is valid using the BoringSSL library.
  std::vector<uint8_t> private_key_bytes(recipient_key_pair.private_key.begin(),
                                         recipient_key_pair.private_key.end());
  std::vector<uint8_t> public_key_bytes(recipient_key_pair.public_key.begin(),
                                        recipient_key_pair.public_key.end());
  std::vector<uint8_t> encap_public_key_bytes(serialized_encapsulated_public_key.begin(),
                                              serialized_encapsulated_public_key.end());

  bssl::ScopedEVP_HPKE_KEY recipient_keys;

  absl::Status keys_valid_status = ValidateKeys(public_key_bytes, private_key_bytes,
                                                encap_public_key_bytes, recipient_keys.get());
  if (!keys_valid_status.ok()) {
    return keys_valid_status;
  }
  std::vector<uint8_t> info_bytes(info.begin(), info.end());

  std::unique_ptr<EVP_HPKE_CTX> hpke_recipient_context(EVP_HPKE_CTX_new());
  if (hpke_recipient_context == nullptr) {
    return absl::AbortedError("Unable to generate HPKE sender context");
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
    return absl::AbortedError("Unable to setup recipient context.");
  }

  // Set up response encryption.
  auto aead_response_context = GetResponseContext(hpke_recipient_context.get());
  if (!aead_response_context.ok()) {
    return aead_response_context.status();
  }

  auto response_nonce = GetResponseBaseNonce(hpke_recipient_context.get());
  if (!response_nonce.ok()) {
    return response_nonce.status();
  }

  // Create recipient request and response contexts.
  RecipientContext recipient_context;

  std::unique_ptr<RecipientRequestContext>& recipient_request_context =
      recipient_context.recipient_request_context;
  recipient_request_context =
      std::make_unique<RecipientRequestContext>(std::move(hpke_recipient_context));

  std::unique_ptr<RecipientResponseContext>& recipient_response_context =
      recipient_context.recipient_response_context;
  recipient_response_context = std::make_unique<RecipientResponseContext>(
      *std::move(aead_response_context), *response_nonce);

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

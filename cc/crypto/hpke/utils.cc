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
#include "cc/crypto/hpke/utils.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/aead.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Oak uses AES-256-GCM AEAD encryption. The bytes come from
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-authenticated-encryption-wi>
constexpr size_t kAeadAlgorithmKeySizeBytes = 32;
constexpr size_t kAeadNonceSizeBytes = 12;

absl::StatusOr<std::unique_ptr<EVP_AEAD_CTX>> GetContext(EVP_HPKE_CTX* hpke_ctx,
                                                         absl::string_view key_context_string) {
  std::vector<uint8_t> key(kAeadAlgorithmKeySizeBytes);
  std::vector<uint8_t> key_context_bytes(key_context_string.begin(), key_context_string.end());

  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_ctx,
          /* out= */ key.data(),
          /* secret_len= */ key.size(),
          /* context= */ key_context_bytes.data(),
          /* context_len= */ key_context_bytes.size())) {
    return absl::AbortedError("Unable to export key.");
  }

  std::unique_ptr<EVP_AEAD_CTX> aead_context(EVP_AEAD_CTX_new(
      /* aead= */ EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()),
      /* key= */ key.data(),
      /* key_len= */ key.size(),
      /* tag_len= */ 0));

  if (aead_context == nullptr) {
    return absl::AbortedError("Unable to generate AEAD context.");
  }

  return std::move(aead_context);
}

absl::StatusOr<std::vector<uint8_t>> GetBaseNonce(EVP_HPKE_CTX* hpke_ctx,
                                                  absl::string_view nonce_context_string) {
  std::vector<uint8_t> nonce(kAeadNonceSizeBytes);
  std::vector<uint8_t> nonce_context_bytes(nonce_context_string.begin(),
                                           nonce_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_ctx,
          /* out= */ nonce.data(),
          /* secret_len= */ nonce.size(),
          /* context= */ nonce_context_bytes.data(),
          /* context_len= */ nonce_context_bytes.size())) {
    return absl::AbortedError("Unable to export nonce");
  }
  return nonce;
}

std::vector<uint8_t> CalculateNonce(const std::vector<uint8_t>& base_nonce,
                                    uint64_t sequence_number) {
  std::vector<uint8_t> nonce(kAeadNonceSizeBytes);
  // We use 8 here since sequence number is 64 bits.
  for (size_t i = 0; i < 8; ++i) {
    // Get the first 8 bits and push bits right since the encoded nonce is big-endian.
    nonce[kAeadNonceSizeBytes - i - 1] = sequence_number & 0xff;
    sequence_number >>= 8;
  }
  // XOR each of the nonce bits with the base nonce.
  for (size_t i = 0; i < kAeadNonceSizeBytes; ++i) {
    nonce[i] ^= base_nonce.at(i);
  }
  return nonce;
}

absl::StatusOr<std::string> AeadSeal(const EVP_AEAD_CTX* context, std::vector<uint8_t> nonce,
                                     absl::string_view plaintext,
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

  if (!EVP_AEAD_CTX_seal(
          /* ctx= */ context,
          /* out= */ ciphertext_bytes.data(),
          /* out_len= */ &ciphertext_bytes_len,
          /* max_out_len= */ ciphertext_bytes.size(),
          /* nonce= */ nonce.data(),
          /* nonce_len= */ nonce.size(),
          /* in= */ plaintext_bytes.data(),
          /* in_len= */ plaintext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Unable to encrypt message");
  }
  ciphertext_bytes.resize(ciphertext_bytes_len);
  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());
  return ciphertext;
}

absl::StatusOr<std::string> AeadOpen(const EVP_AEAD_CTX* context, std::vector<uint8_t> nonce,
                                     absl::string_view ciphertext,
                                     absl::string_view associated_data) {
  std::vector<uint8_t> ciphertext_bytes(ciphertext.begin(), ciphertext.end());
  if (ciphertext_bytes.empty()) {
    return absl::InvalidArgumentError("No ciphertext was provided");
  }
  std::vector<uint8_t> associated_data_bytes(associated_data.begin(), associated_data.end());

  // The plaintext should not be longer than the ciphertext.
  std::vector<uint8_t> plaintext_bytes(ciphertext_bytes.size());
  size_t plaintext_bytes_size;

  if (!EVP_AEAD_CTX_open(
          /* ctx= */ context,
          /* out= */ plaintext_bytes.data(),
          /* out_len= */ &plaintext_bytes_size,
          /* max_out_len= */ ciphertext_bytes.size(),
          /* nonce= */ nonce.data(),
          /* nonce_len= */ nonce.size(),
          /* in= */ ciphertext_bytes.data(),
          /* in_len= */ ciphertext_bytes.size(),
          /* ad= */ associated_data_bytes.data(),
          /* ad_len= */ associated_data_bytes.size())) {
    return absl::AbortedError("Unable to decrypt message");
  }
  plaintext_bytes.resize(plaintext_bytes_size);
  std::string plaintext(plaintext_bytes.begin(), plaintext_bytes.end());
  return plaintext;
}

}  // namespace oak::crypto
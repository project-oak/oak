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

#include "absl/base/attributes.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/aead.h"
#include "openssl/hpke.h"

namespace oak::crypto {

// Oak uses AES-256-GCM AEAD encryption. The bytes come from
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-authenticated-encryption-wi>
constexpr size_t kAeadAlgorithmKeySizeBytes = 32;
constexpr size_t kAeadNonceSizeBytes = 12;

absl::StatusOr<std::unique_ptr<EVP_AEAD_CTX>> GetResponseContext(EVP_HPKE_CTX* hpke_ctx) {
  std::vector<uint8_t> response_key(kAeadAlgorithmKeySizeBytes);
  std::string key_context_string = "response_key";
  std::vector<uint8_t> key_context_bytes(key_context_string.begin(), key_context_string.end());

  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_ctx,
          /* out= */ response_key.data(),
          /* secret_len= */ response_key.size(),
          /* context= */ key_context_bytes.data(),
          /* context_len= */ key_context_bytes.size())) {
    return absl::AbortedError("Unable to export response key.");
  }

  std::unique_ptr<EVP_AEAD_CTX> aead_response_context(EVP_AEAD_CTX_new(
      /* aead= */ EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm()),
      /* key= */ response_key.data(),
      /* key_len= */ response_key.size(),
      /* tag_len= */ 0));

  if (aead_response_context == nullptr) {
    return absl::AbortedError("Unable to generate AEAD response context.");
  }

  return std::move(aead_response_context);
}

absl::StatusOr<std::vector<uint8_t>> GetResponseNonce(EVP_HPKE_CTX* hpke_ctx) {
  std::vector<uint8_t> response_nonce(kAeadNonceSizeBytes);
  std::string nonce_context_string = "response_nonce";
  std::vector<uint8_t> nonce_context_bytes(nonce_context_string.begin(),
                                           nonce_context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_ctx,
          /* out= */ response_nonce.data(),
          /* secret_len= */ response_nonce.size(),
          /* context= */ nonce_context_bytes.data(),
          /* context_len= */ nonce_context_bytes.size())) {
    return absl::AbortedError("Unable to export response nonce.");
  }
  return response_nonce;
}
}  // namespace oak::crypto
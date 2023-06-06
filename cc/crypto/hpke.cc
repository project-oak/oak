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

#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/hpke.h"
#include "util.h"

namespace oak::crypto {

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
  std::unique_ptr<EVP_HPKE_CTX> hpke_request_context(EVP_HPKE_CTX_new());

  std::vector<uint8_t> encap_shared_secret(EVP_HPKE_MAX_ENC_LENGTH);
  size_t encap_shared_secret_len;

  std::vector<uint8_t> recipient_public_key_bytes =
      StringViewToBytes(serialized_recipient_public_key);
  std::vector<uint8_t> info_bytes = StringViewToBytes(info);

  // Create sender context.
  if (!EVP_HPKE_CTX_setup_sender(
          /* ctx= */ hpke_request_context.get(),
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

  // Generate a response key from the receiver context.
  std::vector<uint8_t> response_key(EVP_HPKE_MAX_PRIVATE_KEY_LENGTH);

  std::string context_string = "response_key";
  std::vector<uint8_t> context_bytes(context_string.begin(), context_string.end());
  if (!EVP_HPKE_CTX_export(
          /* ctx= */ hpke_request_context.get(),
          /* out= */ response_key.data(),
          /* secret_len= */ EVP_HPKE_MAX_PRIVATE_KEY_LENGTH,
          /* context= */ context_bytes.data(),
          /* context_len= */ context_bytes.size())) {
    return absl::AbortedError("Unable to export client private key.");
  }

  // EVP_HPKE_CTX* sender_context = EVP_HPKE_CTX_new();
  //    This will require generating a response key and tagging that to the context.
  // Export response key
  // Export response nonce
  // EVP_HPKE_CTX_setup_sender()
  // setup_sender
  std::string encap_key(encap_shared_secret->begin(), encap_shared_secret->end());

  ClientHPKEConfig client_hpke_config;
  return client_hpke_config;
}
}  // namespace oak::crypto

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

#ifndef CC_CRYPTO_HPKE_H_
#define CC_CRYPTO_HPKE_H_

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace oak::crypto {

struct KeyPair {
  std::string private_key;
  std::string public_key;
};

class SenderRequestContext {
 public:
  // Encrypts message with associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> seal(absl::string_view plaintext, absl::string_view associated_data);
};

class SenderResponseContext {
 public:
  // Decrypts response message and validates associated data using AEAD as part of bidirectional
  // communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> open(absl::string_view ciphertext, absl::string_view associated_data);
};

class RecipientRequestContext {
 public:
  // Decrypts message and validates associated data using AEAD.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
  absl::StatusOr<std::string> open(absl::string_view ciphertext, absl::string_view associated_data);
};

class RecipientResponseContext {
 public:
  // Encrypts response message with associated data using AEAD as part of bidirectional
  // communication.
  // <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
  absl::StatusOr<std::string> seal(absl::string_view plaintext, absl::string_view associated_data);
};

// Sets up an HPKE sender by generating an ephemeral keypair (and serializing the corresponding
// public key) and creating a sender context.
// Returns a tuple with an encapsulated public key, sender request and sender response contexts.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
//
// Encapsulated public key is represented as a NIST P-256 SEC1 encoded point public key.
// <https://secg.org/sec1-v2.pdf>
absl::StatusOr<std::tuple<std::string, std::unique_ptr<SenderRequestContext>,
                          std::unique_ptr<SenderResponseContext>>>
setup_base_sender(absl::string_view serialized_recipient_public_key, absl::string_view info);

// Sets up an HPKE recipient by creating a recipient context.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
// Returns a tuple with a recipient request and recipient response contexts.
// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
absl::StatusOr<
    std::tuple<std::unique_ptr<RecipientRequestContext>, std::unique_ptr<RecipientResponseContext>>>
setup_base_recipient(absl::string_view serialized_encapsulated_public_key,
                     KeyPair recipient_key_pair);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_HPKE_H_

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

#ifndef CC_CRYPTO_ENCRYPTION_KEY_H_
#define CC_CRYPTO_ENCRYPTION_KEY_H_

#include <memory>
#include <string>
#include <tuple>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/recipient_context.h"

namespace oak::crypto {

class EncryptionKeyHandle {
 public:
  virtual absl::StatusOr<std::unique_ptr<RecipientContext>>
  GenerateRecipientContext(
      absl::string_view serialized_encapsulated_public_key) = 0;

  virtual ~EncryptionKeyHandle() = default;
};

class EncryptionKeyProvider : public EncryptionKeyHandle {
 public:
  static absl::StatusOr<EncryptionKeyProvider> Create();

  absl::StatusOr<std::unique_ptr<RecipientContext>> GenerateRecipientContext(
      absl::string_view serialized_encapsulated_public_key) override;

  std::string GetSerializedPublicKey() const { return key_pair_.public_key; }

 private:
  KeyPair key_pair_;

  explicit EncryptionKeyProvider(KeyPair key_pair) : key_pair_(key_pair) {}
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_ENCRYPTION_KEY_H_

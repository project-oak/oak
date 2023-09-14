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

#include "cc/crypto/encryption_key_provider.h"

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/hpke/recipient_context.h"

namespace oak::crypto {

absl::StatusOr<std::unique_ptr<EncryptionKeyProvider>> EncryptionKeyProvider::Create() {
  absl::StatusOr<KeyPair> key_pair = KeyPair::Generate();
  if (!key_pair.ok()) {
    return key_pair.status();
  }
  return std::make_unique<EncryptionKeyProvider>(*key_pair);
}

absl::StatusOr<RecipientContext> EncryptionKeyProvider::GenerateRecipientContext(
    absl::string_view serialized_encapsulated_public_key) {
  return SetupBaseRecipient(serialized_encapsulated_public_key, key_pair_, kOakHPKEInfo);
}

}  // namespace oak::crypto

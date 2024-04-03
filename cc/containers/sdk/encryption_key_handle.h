/*
 * Copyright 2024 The Project Oak Authors
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

#ifndef CC_CONTAINERS_SDK_ENCRYPTION_KEY_HANDLE_H_
#define CC_CONTAINERS_SDK_ENCRYPTION_KEY_HANDLE_H_

#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/orchestrator_crypto_client.h"
#include "cc/crypto/encryption_key.h"
#include "cc/crypto/hpke/recipient_context.h"

namespace oak::containers::sdk {

class InstanceEncryptionKeyHandle : public ::oak::crypto::EncryptionKeyHandle {
 public:
  absl::StatusOr<std::unique_ptr<::oak::crypto::RecipientContext>>
  GenerateRecipientContext(
      absl::string_view serialized_encapsulated_public_key) override;

 private:
  OrchestratorCryptoClient orchestrator_crypto_client_;
};

class GroupEncryptionKeyHandle : public ::oak::crypto::EncryptionKeyHandle {
 public:
  absl::StatusOr<std::unique_ptr<::oak::crypto::RecipientContext>>
  GenerateRecipientContext(
      absl::string_view serialized_encapsulated_public_key) override;

 private:
  OrchestratorCryptoClient orchestrator_crypto_client_;
};

}  // namespace oak::containers::sdk

#endif  // THIRD_PARTY_OAK_CC_CONTAINERS_ENCRYPTION_KEY_HANDLE_H_

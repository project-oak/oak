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

#include "cc/containers/sdk/encryption_key_handle.h"

#include <memory>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/recipient_context.h"

namespace oak::containers::sdk {

namespace {
using ::oak::containers::v1::KeyOrigin;
using ::oak::crypto::RecipientContext;
using ::oak::crypto::v1::SessionKeys;
}  // namespace

absl::StatusOr<std::unique_ptr<RecipientContext>>
InstanceEncryptionKeyHandle::GenerateRecipientContext(
    absl::string_view serialized_encapsulated_public_key) {
  absl::StatusOr<SessionKeys> session_keys =
      orchestrator_crypto_client_.DeriveSessionKeys(
          KeyOrigin::INSTANCE, serialized_encapsulated_public_key);
  if (!session_keys.ok()) {
    return absl::InternalError("couldn't derive session keys");
  }

  return RecipientContext::Deserialize(*session_keys);
}

absl::StatusOr<std::unique_ptr<RecipientContext>>
GroupEncryptionKeyHandle::GenerateRecipientContext(
    absl::string_view serialized_encapsulated_public_key) {
  absl::StatusOr<SessionKeys> session_keys =
      orchestrator_crypto_client_.DeriveSessionKeys(
          KeyOrigin::GROUP, serialized_encapsulated_public_key);
  if (!session_keys.ok()) {
    return absl::InternalError("couldn't derive session keys");
  }

  return RecipientContext::Deserialize(*session_keys);
}

}  // namespace oak::containers::sdk

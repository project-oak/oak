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

#include "cc/containers/sdk/signing_key_handle.h"

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace oak::containers::sdk {

namespace {
using ::oak::containers::v1::KeyOrigin;
using ::oak::crypto::v1::Signature;
}  // namespace

absl::StatusOr<Signature> InstanceSigningKeyHandle::Sign(
    absl::string_view message) {
  return orchestrator_crypto_client_.Sign(KeyOrigin::INSTANCE, message);
}

absl::StatusOr<Signature> GroupSigningKeyHandle::Sign(
    absl::string_view message) {
  return orchestrator_crypto_client_.Sign(KeyOrigin::GROUP, message);
}

}  // namespace oak::containers::sdk

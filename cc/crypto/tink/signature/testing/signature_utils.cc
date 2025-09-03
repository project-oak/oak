/*
 * Copyright 2025 The Project Oak Authors
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

#include "cc/crypto/tink/signature/testing/signature_utils.h"

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/status/status.h"
#include "tink/config/global_registry.h"
#include "tink/keyset_handle.h"
#include "tink/proto_keyset_format.h"
#include "tink/public_key_sign.h"
#include "tink/signature/signature_config.h"
#include "tink/signature/signature_key_templates.h"

namespace oak::crypto::tink {

using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::KeyGenConfigGlobalRegistry;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::PublicKeySign;
using ::crypto::tink::SerializeKeysetWithoutSecretToProtoKeysetFormat;
using ::crypto::tink::SignatureConfig;
using ::crypto::tink::SignatureKeyTemplates;
using ::oak::util::status::Annotate;

absl::StatusOr<SignatureWrapper> SignWithTink(absl::string_view message) {
  // 1) Register PublicKeyVerify primitives.
  absl::Status status = SignatureConfig::Register();
  if (!status.ok()) {
    return Annotate(status, "Failed registering Tink signing primities.");
  }

  // 2) Create a keyset handle.
  absl::StatusOr<std::unique_ptr<KeysetHandle>> keyset_handle =
      KeysetHandle::GenerateNew(SignatureKeyTemplates::EcdsaP256(),
                                KeyGenConfigGlobalRegistry());
  if (!keyset_handle.ok()) {
    return Annotate(keyset_handle.status(), "Failed to create keyset handle.");
  }

  // 3) Get the PublicKeySign primitive from the keyset handle.
  absl::StatusOr<std::unique_ptr<PublicKeySign>> public_key_sign =
      (*keyset_handle)->GetPrimitive<PublicKeySign>(ConfigGlobalRegistry());
  if (!public_key_sign.ok()) {
    return Annotate(public_key_sign.status(),
                    "Failed to get PublicKeySign primitive.");
  }

  // 4) Sign the message.
  absl::StatusOr<std::string> signature = (*public_key_sign)->Sign(message);
  if (!signature.ok()) {
    return Annotate(signature.status(), "Failed to sign the message.");
  }

  // 5) Get the public keyset handle, to be used for signature verification.
  absl::StatusOr<std::unique_ptr<KeysetHandle>> public_keyset_handle =
      (*keyset_handle)->GetPublicKeysetHandle(KeyGenConfigGlobalRegistry());
  if (!public_keyset_handle.ok()) {
    return Annotate(public_keyset_handle.status(),
                    "Failed to get the public keyset handle.");
  }

  // 6) Serialize the public keyset handle.
  absl::StatusOr<std::string> serialized_public_keyset_handle =
      SerializeKeysetWithoutSecretToProtoKeysetFormat(**public_keyset_handle);
  if (!serialized_public_keyset_handle.ok()) {
    return Annotate(serialized_public_keyset_handle.status(),
                    "Failed to serialize the public keyset handle.");
  }

  return SignatureWrapper{
      .signature = *signature,
      .tink_public_keyset = *serialized_public_keyset_handle,
  };
}

}  // namespace oak::crypto::tink
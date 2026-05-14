/*
 * Copyright 2026 The Project Oak Authors
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

#include "cc/crypto/tink/signature/ml_dsa_44_utils.h"

#include <memory>
#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/status/status.h"
#include "tink/config/global_registry.h"
#include "tink/insecure_secret_key_access.h"
#include "tink/key_status.h"
#include "tink/keyset_handle.h"
#include "tink/partial_key_access.h"
#include "tink/public_key_sign.h"
#include "tink/public_key_verify.h"
#include "tink/signature/ml_dsa_parameters.h"
#include "tink/signature/ml_dsa_private_key.h"
#include "tink/signature/ml_dsa_public_key.h"
#include "tink/signature/signature_config.h"

namespace oak::crypto::tink {

using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::GetPartialKeyAccess;
using ::crypto::tink::InsecureSecretKeyAccess;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::KeysetHandleBuilder;
using ::crypto::tink::KeyStatus;
using ::crypto::tink::MlDsaParameters;
using ::crypto::tink::MlDsaPrivateKey;
using ::crypto::tink::MlDsaPublicKey;
using ::crypto::tink::PublicKeySign;
using ::crypto::tink::PublicKeyVerify;
using ::crypto::tink::RestrictedData;
using ::crypto::tink::SignatureConfig;
using ::oak::util::status::Annotate;

absl::Status VerifyMlDsa44(absl::string_view message,
                           absl::string_view signature,
                           absl::string_view raw_public_key) {
  // 1) Register signature primitives.
  absl::Status status = SignatureConfig::Register();
  if (!status.ok()) {
    return Annotate(status, "registering Tink signature primitives");
  }

  // 2) Create ML-DSA-44 parameters with no prefix.
  absl::StatusOr<MlDsaParameters> params = MlDsaParameters::Create(
      MlDsaParameters::Instance::kMlDsa44, MlDsaParameters::Variant::kNoPrefix);
  if (!params.ok()) {
    return Annotate(params.status(), "creating ML-DSA-44 parameters");
  }

  // 3) Create the public key from raw bytes.
  absl::StatusOr<MlDsaPublicKey> public_key = MlDsaPublicKey::Create(
      *params, raw_public_key, std::nullopt, GetPartialKeyAccess());
  if (!public_key.ok()) {
    return Annotate(public_key.status(), "creating ML-DSA-44 public key");
  }

  // 4) Build a keyset handle containing the public key.
  absl::StatusOr<KeysetHandle> keyset_handle =
      KeysetHandleBuilder()
          .AddEntry(KeysetHandleBuilder::Entry::CreateFromCopyableKey(
              *public_key, KeyStatus::kEnabled, /*is_primary=*/true))
          .Build();
  if (!keyset_handle.ok()) {
    return Annotate(keyset_handle.status(), "building keyset handle");
  }

  // 5) Get the PublicKeyVerify primitive.
  absl::StatusOr<std::unique_ptr<PublicKeyVerify>> verifier =
      keyset_handle->GetPrimitive<PublicKeyVerify>(ConfigGlobalRegistry());
  if (!verifier.ok()) {
    return Annotate(verifier.status(), "getting PublicKeyVerify primitive");
  }

  // 6) Verify the signature.
  return (*verifier)->Verify(signature, message);
}

absl::StatusOr<std::string> SignMlDsa44(absl::string_view message,
                                        const MlDsa44KeyPair& key_pair) {
  // 1) Register signature primitives.
  absl::Status status = SignatureConfig::Register();
  if (!status.ok()) {
    return Annotate(status, "registering Tink signature primitives");
  }

  // 2) Create ML-DSA-44 parameters with no prefix.
  absl::StatusOr<MlDsaParameters> params = MlDsaParameters::Create(
      MlDsaParameters::Instance::kMlDsa44, MlDsaParameters::Variant::kNoPrefix);
  if (!params.ok()) {
    return Annotate(params.status(), "creating ML-DSA-44 parameters");
  }

  // 3) Create the public key from raw bytes.
  absl::StatusOr<MlDsaPublicKey> public_key = MlDsaPublicKey::Create(
      *params, key_pair.public_key, std::nullopt, GetPartialKeyAccess());
  if (!public_key.ok()) {
    return Annotate(public_key.status(), "creating ML-DSA-44 public key");
  }

  // 4) Create the private key from raw bytes.
  absl::StatusOr<MlDsaPrivateKey> private_key = MlDsaPrivateKey::Create(
      *public_key,
      RestrictedData(key_pair.private_key, InsecureSecretKeyAccess::Get()),
      GetPartialKeyAccess());
  if (!private_key.ok()) {
    return Annotate(private_key.status(), "creating ML-DSA-44 private key");
  }

  // 5) Build a keyset handle containing the private key.
  absl::StatusOr<KeysetHandle> keyset_handle =
      KeysetHandleBuilder()
          .AddEntry(KeysetHandleBuilder::Entry::CreateFromCopyableKey(
              *private_key, KeyStatus::kEnabled, /*is_primary=*/true))
          .Build();
  if (!keyset_handle.ok()) {
    return Annotate(keyset_handle.status(), "building keyset handle");
  }

  // 6) Get the PublicKeySign primitive.
  absl::StatusOr<std::unique_ptr<PublicKeySign>> signer =
      keyset_handle->GetPrimitive<PublicKeySign>(ConfigGlobalRegistry());
  if (!signer.ok()) {
    return Annotate(signer.status(), "getting PublicKeySign primitive");
  }

  // 7) Sign the message.
  return (*signer)->Sign(message);
}

absl::StatusOr<MlDsa44KeyPair> GenerateMlDsa44KeyPair() {
  // 1) Register signature primitives.
  absl::Status status = SignatureConfig::Register();
  if (!status.ok()) {
    return Annotate(status, "registering Tink signature primitives");
  }

  // 2) Create ML-DSA-44 parameters with no prefix.
  absl::StatusOr<MlDsaParameters> params = MlDsaParameters::Create(
      MlDsaParameters::Instance::kMlDsa44, MlDsaParameters::Variant::kNoPrefix);
  if (!params.ok()) {
    return Annotate(params.status(), "creating ML-DSA-44 parameters");
  }

  // 3) Generate a new keyset handle with an ML-DSA-44 key.
  absl::StatusOr<std::unique_ptr<KeysetHandle>> keyset_handle =
      KeysetHandle::GenerateNewFromParameters(
          *params, ::crypto::tink::KeyGenConfigGlobalRegistry());
  if (!keyset_handle.ok()) {
    return Annotate(keyset_handle.status(), "generating ML-DSA-44 keyset");
  }

  // 4) Extract the private key from the primary entry.
  KeysetHandle::Entry entry = (*keyset_handle)->GetPrimary();
  std::shared_ptr<const ::crypto::tink::Key> key = entry.GetKey();
  const MlDsaPrivateKey* private_key =
      dynamic_cast<const MlDsaPrivateKey*>(key.get());
  if (private_key == nullptr) {
    return absl::InternalError("primary key is not an MlDsaPrivateKey");
  }

  // 5) Extract the raw public key bytes.
  absl::StatusOr<absl::string_view> public_key_bytes =
      private_key->GetPublicKey().GetPublicKeyBytes(GetPartialKeyAccess());
  if (!public_key_bytes.ok()) {
    return Annotate(public_key_bytes.status(),
                    "extracting raw public key bytes");
  }

  // 6) Extract the raw private seed bytes.
  const RestrictedData& private_seed_data =
      private_key->GetPrivateSeedBytes(GetPartialKeyAccess());

  return MlDsa44KeyPair{
      .public_key = std::string(*public_key_bytes),
      .private_key = std::string(
          private_seed_data.GetSecret(InsecureSecretKeyAccess::Get())),
  };
}

}  // namespace oak::crypto::tink

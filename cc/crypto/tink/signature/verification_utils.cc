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

#include "cc/crypto/tink/signature/verification_utils.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/cxx_string.h"
#include "cc/utils/status/status.h"
#include "tink/config/global_registry.h"
#include "tink/keyset_handle.h"
#include "tink/proto_keyset_format.h"
#include "tink/public_key_verify.h"

namespace oak::crypto::tink {

using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::ParseKeysetWithoutSecretFromProtoKeysetFormat;
using ::crypto::tink::PublicKeyVerify;
using ::oak::ffi::CxxString;
using ::oak::util::status::Annotate;

absl::Status VerifyTinkDigitalSignature(
    absl::string_view message, absl::string_view signature,
    absl::string_view proto_serialized_signer_public_keyset) {
  // 1) Read keyset into tink object.
  absl::StatusOr<KeysetHandle> keyset_handle =
      ParseKeysetWithoutSecretFromProtoKeysetFormat(
          proto_serialized_signer_public_keyset);
  if (!keyset_handle.ok()) {
    return Annotate(keyset_handle.status(), "Failed to parse keyset");
  }

  // 2) Get the PublicKeyVerify primitive from the keyset handle.
  absl::StatusOr<std::unique_ptr<PublicKeyVerify>> public_key_verify =
      keyset_handle->GetPrimitive<crypto::tink::PublicKeyVerify>(
          ConfigGlobalRegistry());
  if (!public_key_verify.ok()) {
    return Annotate(public_key_verify.status(),
                    "Failed to get PublicKeyVerify primitive");
  }

  // 3) Verify the signature.
  return (*public_key_verify)->Verify(signature, message);
}
}  // namespace oak::crypto::tink

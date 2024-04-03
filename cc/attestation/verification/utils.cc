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

#include "cc/attestation/verification/utils.h"

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/cose/cwt.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::attestation::verification {

namespace {
using ::oak::attestation::v1::Evidence;
using ::oak::utils::cose::Cwt;
}  // namespace

absl::StatusOr<std::string> ExtractPublicKey(absl::string_view certificate) {
  auto cwt = Cwt::Deserialize(certificate);
  if (!cwt.ok()) {
    return cwt.status();
  }
  auto public_key = cwt->subject_public_key.GetPublicKey();
  return std::string(public_key.begin(), public_key.end());
}

absl::StatusOr<std::string> ExtractEncryptionPublicKey(
    const Evidence& evidence) {
  return ExtractPublicKey(
      evidence.application_keys().encryption_public_key_certificate());
}

absl::StatusOr<std::string> ExtractSigningPublicKey(const Evidence& evidence) {
  return ExtractPublicKey(
      evidence.application_keys().signing_public_key_certificate());
}

}  // namespace oak::attestation::verification

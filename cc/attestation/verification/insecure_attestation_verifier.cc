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

#include "cc/attestation/verification/insecure_attestation_verifier.h"

#include <chrono>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/cose/cwt.h"
#include "proto/attestation/endorsement.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"

namespace oak::attestation::verification {

namespace {
using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::v1::Endorsements;
using ::oak::attestation::v1::Evidence;
using ::oak::utils::cose::Cwt;
}  // namespace

absl::StatusOr<AttestationResults> InsecureAttestationVerifier::Verify(
    std::chrono::time_point<std::chrono::system_clock> now, Evidence evidence,
    Endorsements endorsements) const {
  absl::StatusOr<std::string> encryption_public_key =
      ExtractEncryptionPublicKey(evidence.application_keys().encryption_public_key_certificate());
  if (!encryption_public_key.ok()) {
    return encryption_public_key.status();
  }

  AttestationResults attestation_results;
  *attestation_results.mutable_encryption_public_key() = *encryption_public_key;

  return attestation_results;
}

absl::StatusOr<std::string> InsecureAttestationVerifier::ExtractEncryptionPublicKey(
    absl::string_view certificate) const {
  auto cwt = Cwt::Deserialize(certificate);
  if (!cwt.ok()) {
    return cwt.status();
  }
  auto public_key = cwt->subject_public_key.GetPublicKey();
  return std::string(public_key.begin(), public_key.end());
}

}  // namespace oak::attestation::verification

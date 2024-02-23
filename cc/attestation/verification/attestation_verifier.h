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

#ifndef CC_ATTESTATION_VERIFICATION_ATTESTATION_VERIFIER_H_
#define CC_ATTESTATION_VERIFICATION_ATTESTATION_VERIFIER_H_

#include <chrono>

#include "absl/status/statusor.h"
#include "proto/attestation/endorsement.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"

namespace oak::attestation::verification {

// Abstract class implementing the functionality of a verifier that appraises
// the attestation evidence and produces an attestation result.
// <https://www.rfc-editor.org/rfc/rfc9334.html#name-verifier>
class AttestationVerifier {
 public:
  virtual ~AttestationVerifier() = default;

  virtual absl::StatusOr<::oak::attestation::v1::AttestationResults> Verify(
      std::chrono::time_point<std::chrono::system_clock> now,
      const ::oak::attestation::v1::Evidence& evidence,
      const ::oak::attestation::v1::Endorsements& endorsements) const = 0;
};

}  // namespace oak::attestation::verification

#endif  // CC_ATTESTATION_VERIFICATION_ATTESTATION_VERIFIER_H_

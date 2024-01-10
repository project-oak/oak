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

#ifndef CC_REMOTE_ATTESTATION_ATTESTATION_VERIFIER_H_
#define CC_REMOTE_ATTESTATION_ATTESTATION_VERIFIER_H_

#include <string>

#include "absl/status/status.h"
#include "proto/session/messages.pb.h"

namespace oak::remote_attestation {

// Abstract class implementing the functionality of a verifier that appraises
// the attestation evidence and produces an attestation result.
// <https://www.rfc-editor.org/rfc/rfc9334.html#name-verifier>
class AttestationVerifier {
 public:
  virtual ~AttestationVerifier() = default;

  // Verify that the provided evidence was endorsed and contains specified
  // reference values.
  //
  // The statuses returned include the following:
  // - Status::kOk = Trusted Execution Environment was successfully verified with
  //   the references.
  //
  // - Status::kUnauthenticated = Trusted Execution Environment could not be
  //   verified with the references. This may be because the Trusted Execution
  //   Environment is not trustworth or the supplied references were not
  //   sufficient.
  virtual absl::Status Verify(::oak::session::v1::AttestationEvidence evidence,
                              ::oak::session::v1::AttestationEndorsement endorsement) const = 0;
};

}  // namespace oak::remote_attestation

#endif  // CC_REMOTE_ATTESTATION_ATTESTATION_VERIFIER_H_
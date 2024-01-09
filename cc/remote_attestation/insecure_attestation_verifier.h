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

#ifndef CC_REMOTE_ATTESTATION_INSECURE_ATTESTATION_VERIFIER_H_
#define CC_REMOTE_ATTESTATION_INSECURE_ATTESTATION_VERIFIER_H_

#include <string>

#include "absl/status/status.h"
#include "cc/remote_attestation/attestation_verifier.h"
#include "proto/session/v1/messages.pb.h"

namespace oak::remote_attestation {

// Cerifier implementation that doesn't verify attestation evidence and is used for testing.
class InsecureAttestationVerifier : public AttestationVerifier {
 public:
  // Doesn't perform attestation verification and just returns a success value.
  absl::Status Verify(::oak::session::v1::AttestationEvidence evidence,
                      ::oak::session::v1::AttestationEndorsement endorsement) const override;
};

}  // namespace oak::remote_attestation

#endif  // CC_REMOTE_ATTESTATION_INSECURE_ATTESTATION_VERIFIER_H_
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

#include "cc/remote_attestation/insecure_attestation_verifier.h"

#include <string>

#include "absl/status/status.h"
#include "proto/session/v1/messages.pb.h"

namespace oak::remote_attestation {

namespace {
using ::oak::session::v1::AttestationEndorsement;
using ::oak::session::v1::AttestationEvidence;
}  // namespace

absl::Status InsecureAttestationVerifier::Verify(AttestationEvidence evidence,
                                                 AttestationEndorsement endorsement) const {
  return absl::OkStatus();
}

}  // namespace oak::remote_attestation

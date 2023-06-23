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

#ifndef CC_CLIENT_VERIFIER_H_
#define CC_CLIENT_VERIFIER_H_

#include <string>

#include "absl/status/status.h"
#include "cc/client/evidence_provider.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::oak_client {

// Reference values used by the verifier to validate the attestation evidence.
// This comes from
// https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values.
struct ReferenceValue {
  std::string binary_hash;
};

// Abstract class for verifying the attestation evidence and producing an
// attestation result in the form of a status.
class Verifier {
 public:
  virtual ~Verifier() = default;

  // Verifies the attestation evidence and produces an absl::Status. The
  // statuses returned include the following:
  //
  //  Status::kOk = Trusted Execution Environment was successfully verified with
  //  the references.
  //
  //  Status::kUnauthenticated = Trusted Execution Environment could not be
  //  verified with the references. This may be because the Trusted Execution
  //  Environment is not trustworth or the supplied references were not
  //  sufficient.
  virtual absl::Status Verify(::oak::session::v1::AttestationBundle& evidence,
                              ReferenceValue& reference) const = 0;
};

}  // namespace oak::oak_client

#endif  // CC_CLIENT_VERIFIER_H_
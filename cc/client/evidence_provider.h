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

#ifndef CC_OAK_CLIENT_EVIDENCE_PROVIDER_H_
#define CC_OAK_CLIENT_EVIDENCE_PROVIDER_H_

#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::oak_client {

using ::oak::session::v1::AttestationBundle;

// Abstract class for fetching the enclave's public key, attestation report, and
// other metadata needed to for the Verifier class.
class EvidenceProvider {
 public:
  virtual ~EvidenceProvider() = default;

  // Collects evidence that may be present on the device or on the server.
  virtual absl::StatusOr<AttestationBundle> GetEvidence() = 0;
};

}  // namespace oak::oak_client

#endif  // CC_OAK_CLIENT_EVIDENCE_PROVIDER_H_
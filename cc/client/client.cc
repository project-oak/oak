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

#include "cc/client/client.h"

#include <memory>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::client {

namespace {
using ::oak::remote_attestation::AttestationVerifier;
using ::oak::transport::TransportWrapper;
}  // namespace

absl::StatusOr<std::unique_ptr<OakClient>> OakClient::Create(
    std::unique_ptr<TransportWrapper> transport, AttestationVerifier& verifier) {
  absl::StatusOr<::oak::session::v1::AttestationBundle> endorsed_evidence =
      transport->GetEvidence();
  if (!endorsed_evidence.ok()) {
    return endorsed_evidence.status();
  }

  absl::Status verification_status = verifier.Verify(endorsed_evidence->attestation_evidence(),
                                                     endorsed_evidence->attestation_endorsement());
  if (!verification_status.ok()) {
    return verification_status;
  }

  return absl::WrapUnique(new OakClient(
      std::move(transport), endorsed_evidence->attestation_evidence().encryption_public_key()));
}

absl::StatusOr<std::string> OakClient::Invoke(absl::string_view request_body) {
  // TODO(#4069): Implement sending an encrypted request and decrypting the response.
  return absl::OkStatus();
}

}  // namespace oak::client

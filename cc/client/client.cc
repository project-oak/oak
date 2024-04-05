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

#include <chrono>
#include <memory>
#include <string>
#include <utility>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/attestation/verification/attestation_verifier.h"
#include "cc/crypto/client_encryptor.h"
#include "cc/crypto/common.h"
#include "proto/attestation/endorsement.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"

namespace oak::client {

namespace {
using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::verification::AttestationVerifier;
using ::oak::crypto::ClientEncryptor;
using ::oak::crypto::DecryptionResult;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::transport::TransportWrapper;
}  // namespace

constexpr absl::string_view kEmptyAssociatedData = "";

absl::StatusOr<std::unique_ptr<OakClient>> OakClient::Create(
    std::unique_ptr<TransportWrapper> transport,
    AttestationVerifier& verifier) {
  absl::StatusOr<EndorsedEvidence> endorsed_evidence =
      transport->GetEndorsedEvidence();
  if (!endorsed_evidence.ok()) {
    return endorsed_evidence.status();
  }

  absl::StatusOr<AttestationResults> attestation_results = verifier.Verify(
      std::chrono::system_clock::now(), endorsed_evidence->evidence(),
      endorsed_evidence->endorsements());
  if (!attestation_results.ok()) {
    return attestation_results.status();
  }

  switch (attestation_results->status()) {
    case AttestationResults::STATUS_SUCCESS:
      return absl::WrapUnique(new OakClient(
          std::move(transport), attestation_results->encryption_public_key()));
    case AttestationResults::STATUS_GENERIC_FAILURE:
      return absl::FailedPreconditionError(
          absl::StrCat("couldn't verify endorsed evidence: ",
                       attestation_results->reason()));
    case AttestationResults::STATUS_UNSPECIFIED:
    default:
      return absl::InternalError("illegal status code in attestation results");
  }
}

absl::StatusOr<std::string> OakClient::Invoke(absl::string_view request_body) {
  // Create client encryptor.
  absl::StatusOr<std::unique_ptr<ClientEncryptor>> client_encryptor =
      ClientEncryptor::Create(server_encryption_public_key_);
  if (!client_encryptor.ok()) {
    return client_encryptor.status();
  }

  // Encrypt request.
  absl::StatusOr<EncryptedRequest> encrypted_request =
      (*client_encryptor)->Encrypt(request_body, kEmptyAssociatedData);
  if (!encrypted_request.ok()) {
    return encrypted_request.status();
  }

  // Send request.
  absl::StatusOr<EncryptedResponse> encrypted_response =
      transport_->Invoke(*encrypted_request);
  if (!encrypted_response.ok()) {
    return encrypted_response.status();
  }

  // Decrypt response.
  absl::StatusOr<DecryptionResult> response =
      (*client_encryptor)->Decrypt(*encrypted_response);
  if (!response.ok()) {
    return response.status();
  }

  return response->plaintext;
}

}  // namespace oak::client

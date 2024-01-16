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
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/client_encryptor.h"
#include "cc/crypto/common.h"
#include "oak_crypto/proto/v1/crypto.pb.h"
#include "proto/session/messages.pb.h"

namespace oak::client {

namespace {
using ::oak::crypto::ClientEncryptor;
using ::oak::crypto::DecryptionResult;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::remote_attestation::AttestationVerifier;
using ::oak::session::v1::AttestationBundle;
using ::oak::transport::TransportWrapper;
}  // namespace

constexpr absl::string_view kEmptyAssociatedData = "";

absl::StatusOr<std::unique_ptr<OakClient>> OakClient::Create(
    std::unique_ptr<TransportWrapper> transport, AttestationVerifier& verifier) {
  absl::StatusOr<AttestationBundle> endorsed_evidence = transport->GetEvidence();
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
  absl::StatusOr<EncryptedResponse> encrypted_response = transport_->Invoke(*encrypted_request);
  if (!encrypted_response.ok()) {
    return encrypted_response.status();
  }

  // Decrypt response.
  absl::StatusOr<DecryptionResult> response = (*client_encryptor)->Decrypt(*encrypted_response);
  if (!response.ok()) {
    return response.status();
  }

  return response->plaintext;
}

}  // namespace oak::client

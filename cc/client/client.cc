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

#include <string>
#include <utility>

#include "cc/client/evidence_provider.h"
#include "cc/client/verifier.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::oak_client {

namespace {
using ::oak::session::v1::AttestationBundle;
}

absl::StatusOr<OakClient> OakClientBuilder::Build() {
  absl::StatusOr<AttestationBundle> enclave_evidence = evidence_provider_->GetEvidence();
  if (!enclave_evidence.ok()) {
    return enclave_evidence.status();
  }
  absl::Status verification_status = verifier_->Verify(*enclave_evidence, reference_);
  if (!verification_status.ok()) {
    return verification_status;
  }

  crypto_provider_->SetEnclavePublicKey(
      enclave_evidence->attestation_evidence().encryption_public_key());

  OakClient oak_client(std::move(transport_), std::move(crypto_provider_));
  return oak_client;
}

absl::StatusOr<std::string> OakClient::Invoke(std::string request_bytes) {
  absl::StatusOr<std::string> encrypted_request =
      crypto_provider_->GetEncryptor()->Encrypt(request_bytes);
  if (!encrypted_request.ok()) {
    return encrypted_request.status();
  }
  absl::StatusOr<std::string> encrypted_response = transport_->Invoke(*encrypted_request);
  auto decrypted_response = crypto_provider_->GetDecryptor()->Decrypt(*encrypted_response);
  if (!decrypted_response.ok()) {
    return decrypted_response.status();
  }
  return *decrypted_response;
}

}  // namespace oak::oak_client
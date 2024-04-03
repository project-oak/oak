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

#ifndef CC_TRANSPORT_TRANSPORT_H_
#define CC_TRANSPORT_TRANSPORT_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"

namespace oak::transport {

// Abstract class for providing an enclave evidence.
class EvidenceProvider {
 public:
  virtual ~EvidenceProvider() = default;

  // Returns evidence about the trustworthiness of a remote server.
  virtual absl::StatusOr<::oak::session::v1::EndorsedEvidence>
  GetEndorsedEvidence() = 0;
};

// Abstract class for sending messages to the enclave.
class Transport {
 public:
  virtual ~Transport() = default;

  // Sends a request to the enclave and returns a response.
  virtual absl::StatusOr<::oak::crypto::v1::EncryptedResponse> Invoke(
      const oak::crypto::v1::EncryptedRequest& encrypted_request) = 0;
};

// Wrapper for `EvidenceProvider` and `Transport` abstract classes.
class TransportWrapper : public EvidenceProvider, public Transport {
 public:
  virtual ~TransportWrapper() = default;
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_TRANSPORT_H_

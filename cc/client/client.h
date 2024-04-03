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

#ifndef CC_CLIENT_CLIENT_H_
#define CC_CLIENT_CLIENT_H_

#include <memory>
#include <string>

#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/attestation/verification/attestation_verifier.h"
#include "cc/transport/transport.h"
#include "proto/attestation/endorsement.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"

namespace oak::client {

// Oak Client class for exchanging encrypted messages with an Oak Enclave which
// is being run by the Oak Launcher.
class OakClient {
 public:
  // Create an instance of the Oak Client by remotely attesting an Oak Enclave
  // and creating an encrypted channel.
  static absl::StatusOr<std::unique_ptr<OakClient>> Create(
      std::unique_ptr<::oak::transport::TransportWrapper> transport,
      ::oak::attestation::verification::AttestationVerifier& verifier);

  // Invoke the provided method by fetching and verifying the attested enclave
  // public key, and then using it to encrypt the request body.
  absl::StatusOr<std::string> Invoke(absl::string_view request_body);

 private:
  std::unique_ptr<oak::transport::Transport> transport_;
  // TODO(#4157): Store client encryptor once crypto sessions are implemented on
  // the server.
  std::string server_encryption_public_key_;

  OakClient(std::unique_ptr<oak::transport::Transport> transport,
            absl::string_view server_encryption_public_key)
      : transport_(std::move(transport)),
        server_encryption_public_key_(server_encryption_public_key) {}
};

}  // namespace oak::client

#endif  // CC_CLIENT_CLIENT_H_

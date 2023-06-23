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

#ifndef CC_OAK_CLIENT_OAK_CLIENT_H_
#define CC_OAK_CLIENT_OAK_CLIENT_H_

#include <memory>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "cc/client/crypto_provider.h"
#include "cc/client/evidence_provider.h"
#include "cc/client/verifier.h"
#include "cc/transport/transport.h"

namespace oak::oak_client {

// Oak client class for communicating with a Trusted Execution Environment.
class OakClient {
 public:
  // This constructor should only ever be called by the OakClientBuilder.
  OakClient(std::unique_ptr<Transport> transport, std::unique_ptr<CryptoProvider> crypto_provider);

  // Encrypts the request bytes and sends it to the Trusted Execution
  // Environment. The encrypted response from the Trusted Execution Environment
  // is decrypted and the returned. A failed status is returned if there is an
  // error issuing the encrypted request.
  absl::StatusOr<std::string> Invoke(std::string request_bytes);

 private:
  std::unique_ptr<Transport> transport_;
  std::unique_ptr<CryptoProvider> crypto_provider_;
};

// IMPORTANT: transport and crypto_provider parameters are ultimatley passed to
// the generated OakClient so each must be a unique pointer.
class OakClientBuilder {
 public:
  // Constructs an OakClientBuilder from all necessary components.
  OakClientBuilder(EvidenceProvider* evidence_provider, Verifier* verifier,
                   ReferenceValue& reference, std::unique_ptr<Transport> transport,
                   std::unique_ptr<CryptoProvider> crypto_provider)
      : evidence_provider_(evidence_provider),
        verifier_(verifier),
        reference_(reference),
        transport_(std::move(transport)),
        crypto_provider_(std::move(crypto_provider)) {}

  absl::StatusOr<OakClient> Build();

 private:
  EvidenceProvider* evidence_provider_;
  Verifier* verifier_;
  ReferenceValue& reference_;
  std::unique_ptr<Transport> transport_;
  std::unique_ptr<CryptoProvider> crypto_provider_;
};

}  // namespace oak::oak_client

#endif  // CC_OAK_CLIENT_OAK_CLIENT_H_

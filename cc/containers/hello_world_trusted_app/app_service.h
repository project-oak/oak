/*
 * Copyright 2024 The Project Oak Authors
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
#ifndef CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_
#define CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_

#include <string>

#include "absl/log/die_if_null.h"
#include "absl/log/log.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/encryption_key_handle.h"
#include "cc/containers/sdk/orchestrator_client.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers_examples/hello_world/proto/hello_world.grpc.pb.h"
#include "oak_containers_examples/hello_world/proto/hello_world.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

class TrustedApplicationImpl
    : public containers::example::TrustedApplication::Service {
 public:
  TrustedApplicationImpl(
      std::unique_ptr<::oak::crypto::EncryptionKeyHandle> encryption_key_handle,
      oak::session::v1::EndorsedEvidence endorsed_evidence,
      absl::string_view application_config)
      : encryption_key_handle_(std::move(encryption_key_handle)),
        endorsed_evidence_(endorsed_evidence),
        application_config_(application_config) {}

  grpc::Status Session(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<oak::session::v1::ResponseWrapper,
                               oak::session::v1::RequestWrapper>* stream)
      override;

 private:
  std::unique_ptr<::oak::crypto::EncryptionKeyHandle> encryption_key_handle_;
  const oak::session::v1::EndorsedEvidence endorsed_evidence_;
  const std::string application_config_;

  absl::StatusOr<oak::crypto::v1::EncryptedResponse> HandleRequest(
      const oak::crypto::v1::EncryptedRequest& encrypted_request) const;
};

}  // namespace oak::oak_containers_hello_world_trusted_app

#endif  // CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_

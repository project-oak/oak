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
#include "cc/containers/hello_world_trusted_app/app_service.h"

#include <string>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/server_encryptor.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers_hello_world_trusted_app/proto/interface.grpc.pb.h"
#include "oak_containers_hello_world_trusted_app/proto/interface.pb.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

using ::oak::containers::example::HelloRequest;
using ::oak::containers::example::HelloResponse;
using ::oak::crypto::DecryptionResult;
using ::oak::crypto::ServerEncryptor;
using ::oak::crypto::v1::EncryptedResponse;

constexpr absl::string_view kEmptyAssociatedData = "";

grpc::Status TrustedApplicationImpl::Hello(grpc::ServerContext* context,
                                           const HelloRequest* request,
                                           HelloResponse* response) {
  ServerEncryptor server_encryptor(*encryption_key_handle_);
  absl::StatusOr<DecryptionResult> decrypted_request =
      server_encryptor.Decrypt(request->encrypted_request());
  if (!decrypted_request.ok()) {
    return grpc::Status(
        static_cast<grpc::StatusCode>(decrypted_request.status().code()),
        std::string(decrypted_request.status().message()));
  }

  std::string greeting = absl::StrCat(
      "Hello from the trusted side, ", decrypted_request->plaintext,
      "! Btw, the Trusted App has a config with a length of ",
      application_config_.size(), " bytes.");
  absl::StatusOr<EncryptedResponse> encrypted_response =
      server_encryptor.Encrypt(greeting, kEmptyAssociatedData);
  if (!encrypted_response.ok()) {
    return grpc::Status(
        static_cast<grpc::StatusCode>(encrypted_response.status().code()),
        std::string(encrypted_response.status().message()));
  }

  *response->mutable_encrypted_response() = *std::move(encrypted_response);
  return grpc::Status::OK;
}

}  // namespace oak::oak_containers_hello_world_trusted_app

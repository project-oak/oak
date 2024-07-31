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

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/orchestrator_client.h"
#include "cc/crypto/common.h"
#include "cc/crypto/server_encryptor.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers_examples/hello_world/proto/hello_world.grpc.pb.h"
#include "oak_containers_examples/hello_world/proto/hello_world.pb.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/service_streaming.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

using ::oak::crypto::DecryptionResult;
using ::oak::crypto::ServerEncryptor;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;

constexpr absl::string_view kEmptyAssociatedData = "";

grpc::Status TrustedApplicationImpl::Session(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<ResponseWrapper, RequestWrapper>* stream) {
  RequestWrapper request;
  ResponseWrapper response;
  std::clog << "New streaming session starting...";
  stream->SendInitialMetadata();
  while (stream->Read(&request)) {
    switch (request.request_case()) {
      case RequestWrapper::RequestCase::kGetEndorsedEvidenceRequest: {
        *(response.mutable_get_endorsed_evidence_response()
              ->mutable_endorsed_evidence()) = endorsed_evidence_;
        stream->Write(response);
        break;
      }
      case RequestWrapper::RequestCase::kInvokeRequest: {
        auto encrypted_response =
            HandleRequest(request.invoke_request().encrypted_request());
        if (!encrypted_response.ok()) {
          return grpc::Status(
              static_cast<grpc::StatusCode>(encrypted_response.status().code()),
              std::string(encrypted_response.status().message()));
        }
        *(response.mutable_invoke_response()->mutable_encrypted_response()) =
            *encrypted_response;
        stream->Write(response);
        break;
      }
      default:
        return grpc::Status(grpc::INVALID_ARGUMENT, "unknown request type");
    }
  }
  return grpc::Status::OK;
}

absl::StatusOr<EncryptedResponse> TrustedApplicationImpl::HandleRequest(
    const EncryptedRequest& encrypted_request) const {
  ServerEncryptor server_encryptor(*encryption_key_handle_);
  absl::StatusOr<DecryptionResult> decrypted_request =
      server_encryptor.Decrypt(encrypted_request);
  if (!decrypted_request.ok()) {
    return decrypted_request.status();
  }

  std::string greeting = absl::StrCat(
      "Hello from the trusted side, ", decrypted_request->plaintext,
      "! Btw, the Trusted App has a config with a length of ",
      application_config_.size(), " bytes.");

  absl::StatusOr<EncryptedResponse> encrypted_response =
      server_encryptor.Encrypt(greeting, kEmptyAssociatedData);
  return encrypted_response;
}

}  // namespace oak::oak_containers_hello_world_trusted_app

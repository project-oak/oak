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

#ifndef CC_TRANSPORT_GRPC_UNARY_TRANSPORT_H_
#define CC_TRANSPORT_GRPC_UNARY_TRANSPORT_H_

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/transport/transport.h"
#include "cc/transport/util.h"
#include "grpcpp/client_context.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"
#include "proto/session/service_unary.pb.h"

namespace oak::transport {

// Transport class for communication with unary gRPC Oak service. Evidence
// must be collected from the enclave and verified prior to issuing any data
// requests. This template class can be used to communicate with any unary
// stubby Oak service that use a gRPC interface consistent with
// oak/proto/session/service_unary.proto.
template <typename OakBackendStub>
class GrpcUnaryTransport : public ::oak::transport::TransportWrapper {
 public:
  explicit GrpcUnaryTransport(OakBackendStub* const client_stub)
      : client_stub_(client_stub) {}

  // Collects the enclave's evidence that needs to be verified by the client.
  absl::StatusOr<::oak::session::v1::EndorsedEvidence> GetEndorsedEvidence()
      override {
    ::grpc::ClientContext context;
    ::oak::session::v1::GetEndorsedEvidenceRequest request;
    ::oak::session::v1::GetEndorsedEvidenceResponse response;

    grpc::Status status =
        client_stub_->GetEndorsedEvidence(&context, request, &response);
    if (!status.ok()) {
      absl::Status absl_status = to_absl_status(status);
      LOG(ERROR) << "Failed to fetch evidence with status: " << absl_status;
      return absl_status;
    }

    return response.endorsed_evidence();
  }

  // Takes an encrypted request and sends it to the enclave, returning the
  // enclave's encrypted response.
  absl::StatusOr<::oak::crypto::v1::EncryptedResponse> Invoke(
      const ::oak::crypto::v1::EncryptedRequest& encrypted_request) override {
    ::grpc::ClientContext context;
    ::oak::session::v1::InvokeRequest request;
    ::oak::session::v1::InvokeResponse response;

    *request.mutable_encrypted_request() = encrypted_request;
    grpc::Status status = client_stub_->Invoke(&context, request, &response);
    if (!status.ok()) {
      absl::Status absl_status = to_absl_status(status);
      LOG(ERROR) << "Failed to call invoke with status: " << absl_status;
      return absl_status;
    }

    return response.encrypted_response();
  }

 private:
  OakBackendStub* client_stub_;
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_GRPC_UNARY_TRANSPORT_H_

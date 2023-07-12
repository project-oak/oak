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

#ifndef CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_
#define CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_

#include <grpc/grpc.h>
#include <grpcpp/channel.h>
#include <grpcpp/client_context.h>
#include <grpcpp/create_channel.h>
#include <grpcpp/grpcpp.h>

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/transport/transport.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"
#include "oak_remote_attestation/proto/v1/service_streaming.grpc.pb.h"
#include "oak_remote_attestation/proto/v1/service_streaming.pb.h"

namespace oak::transport {

class GrpcStreamingTransport : public TransportWrapper {
 public:
  explicit GrpcStreamingTransport(
      std::unique_ptr<::grpc::ClientReaderWriter<::oak::session::v1::RequestWrapper,
                                                 ::oak::session::v1::ResponseWrapper>>
          channel_reader_writer)
      : channel_reader_writer_(std::move(channel_reader_writer)) {}

  absl::StatusOr<::oak::session::v1::AttestationBundle> GetEvidence() override {
    // Create request.
    ::oak::session::v1::RequestWrapper request;
    ::oak::session::v1::GetPublicKeyRequest get_public_key_request;
    *request.mutable_get_public_key_request() = get_public_key_request;

    // Send request.
    auto response = Send(request);
    if (!response.ok()) {
      return response.status();
    }

    // Process response.
    switch (response->response_case()) {
      case ::oak::session::v1::ResponseWrapper::kGetPublicKeyResponseFieldNumber:
        return response->get_public_key_response().attestation_bundle();
      case ::oak::session::v1::ResponseWrapper::kInvokeResponseFieldNumber:
        return absl::InternalError("received InvokeResponse instead of GetPublicKeyResponse");
      case ::oak::session::v1::ResponseWrapper::RESPONSE_NOT_SET:
        return absl::InternalError("received empty response");
      default:
        return absl::InternalError("received unsupported response type");
    }
  }

  absl::StatusOr<std::string> Invoke(absl::string_view request_bytes) override {
    // Create request.
    ::oak::session::v1::RequestWrapper request;
    ::oak::session::v1::InvokeRequest* invoke_request = request.mutable_invoke_request();
    invoke_request->set_encrypted_body(request_bytes);

    // Send request.
    auto response = Send(request);
    if (!response.ok()) {
      return response.status();
    }

    // Process response.
    switch (response->response_case()) {
      case ::oak::session::v1::ResponseWrapper::kGetPublicKeyResponseFieldNumber:
        return absl::InternalError("received GetPublicKeyResponse instead of InvokeResponse");
      case ::oak::session::v1::ResponseWrapper::kInvokeResponseFieldNumber:
        return response->invoke_response().encrypted_body();
      case ::oak::session::v1::ResponseWrapper::RESPONSE_NOT_SET:
        return absl::InternalError("received empty response");
      default:
        return absl::InternalError("received unsupported response type");
    }
  }

 private:
  std::unique_ptr<::grpc::ClientReaderWriter<::oak::session::v1::RequestWrapper,
                                             ::oak::session::v1::ResponseWrapper>>
      channel_reader_writer_;

  absl::StatusOr<::oak::session::v1::ResponseWrapper> Send(
      const ::oak::session::v1::RequestWrapper& request) {
    // Send a request.
    channel_reader_writer_->Write(request);
    channel_reader_writer_->WritesDone();

    // Receive a response.
    ::oak::session::v1::ResponseWrapper response;
    channel_reader_writer_->Read(&response);
    ::grpc::Status status = channel_reader_writer_->Finish();
    if (status.ok()) {
      return response;
    } else {
      return absl::InternalError("couldn't send request: " + status.error_message());
    }
  }
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_

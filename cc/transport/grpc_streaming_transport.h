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

#include <grpcpp/grpcpp.h>

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/transport/transport.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::transport {

template <class Service>
class GrpcStreamingTransport : public TransportWrapper {
 public:
  // explicit GrpcStreamingTransport(std::shared_ptr<grpc::Channel> channel)
  //     : channel_stub_(Service::NewStub(channel)) {}

  explicit GrpcStreamingTransport(
      std::unique_ptr<::grpc::ClientReaderWriter<::oak::session::v1::RequestWrapper,
                                                 ::oak::session::v1::ResponseWrapper>>
          channel_writer)
      : channel_writer_(std::move(channel_writer));

  absl::StatusOr<::oak::session::v1::AttestationBundle> GetEvidence() override {
    ::oak::session::v1::RequestWrapper request_wrapper;
    ::oak::session::v1::GetPublicKeyRequest get_public_key_request;
    *request_wrapper.mutable_get_public_key_request() = get_public_key_request;

    auto response_status = Send(request_wrapper);
    if (!response_status.ok()) {
      return response_status;
    }

    switch (response_wrapper.response_case()) {
      case ResponseWrapper::kGetPublicKeyResponseFieldNumber:
    return response_status.get_public_key_response().attestation_bundle();
      case ResponseWrapper::kInvokeResponseFieldNumber:
        return absl::InternalError("received InvokeResponse instead of GetPublicKeyResponse");
      case ResponseWrapper::RESPONSE_NOT_SET:
        return absl::InternalError("received empty response");
      default:
        return absl::InternalError("received unsupported response type");
    }

    // ::oak::session::v1::GetPublicKeyRequest request;
    // ::oak::session::v1::GetPublicKeyResponse response;
    // grpc::ClientContext context;

    // grpc::Status status = channel_stub_->GetPublicKey(&context, request, &response);
    // if (!status.ok()) {
    //   return absl::InternalError("couldn't send GetPublicKeyRequest: " + status.error_message());
    // }

    // return response.attestation_bundle();
  }

  absl::StatusOr<std::string> Invoke(absl::string_view request_bytes) override {
    ::oak::session::v1::RequestWrapper request;
    auto* invoke_request = request_wrapper.mutable_invoke_request();
    invoke_request->set_encrypted_body(request_bytes);

    auto response_status = Send(request_wrapper);
    if (!response_status.ok()) {
      return response_status;
    }

    switch (response_wrapper.response_case()) {
      case ResponseWrapper::kGetPublicKeyResponseFieldNumber:
        return absl::InternalError("received GetPublicKeyResponse instead of InvokeResponse");
      case ResponseWrapper::kInvokeResponseFieldNumber:
        return response_wrapper.invoke_response().encrypted_body();
      case ResponseWrapper::RESPONSE_NOT_SET:
        return absl::InternalError("received empty response");
      default:
        return absl::InternalError("received unsupported response type");
    }

    // return response_status.invoke_response().encrypted_body();

    // ::oak::session::v1::InvokeRequest request;
    // request.set_encrypted_body(request_bytes);
    // ::oak::session::v1::InvokeResponse response;
    // grpc::ClientContext context;

    // grpc::Status status = channel_stub_->Invoke(&context, request, &response);
    // if (!status.ok()) {
    //   return absl::InternalError("couldn't send InvokeRequest: " + status.error_message());
    // }

    // return response.encrypted_body();
  }

 private:
  // std::unique_ptr<Service> channel_stub_;
  std::unique_ptr<Service> channel_writer_;
  
  absl::StatusOr<::oak::session::v1::ResponseWrapper> Send(const ::oak::session::v1::RequestWrapper& request) {
    // Send a request.
    RequestWrapper request_wrapper;
    auto* request = request_wrapper.mutable_invoke_request();
    request->set_encrypted_body(request_body);
    reader_writer->Write(request_wrapper);
    reader_writer->WritesDone();

    // Receive a response.
    ResponseWrapper response_wrapper;
    reader_writer->Read(&response_wrapper);
    Status status = reader_writer->Finish();
    if (status.ok()) {
      return response_wrapper;
    } else {
      return absl::InternalError("couldn't send request: " + status.error_message());
    }
  }
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_

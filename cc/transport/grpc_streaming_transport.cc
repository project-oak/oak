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

#include "cc/transport/grpc_streaming_transport.h"

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/grpcpp.h"

namespace oak::transport {

namespace {
using ::oak::session::v1::AttestationBundle;
using ::oak::session::v1::GetPublicKeyRequest;
using ::oak::session::v1::InvokeRequest;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;
}  // namespace

absl::StatusOr<AttestationBundle> GrpcStreamingTransport::GetEvidence() {
  // Create request.
  RequestWrapper request;
  GetPublicKeyRequest get_public_key_request;
  *request.mutable_get_public_key_request() = get_public_key_request;

  // Send request.
  auto response = Send(request);
  if (!response.ok()) {
    return response.status();
  }

  // Process response.
  switch (response->response_case()) {
    case ResponseWrapper::kGetPublicKeyResponseFieldNumber:
      return response->get_public_key_response().attestation_bundle();
    case ResponseWrapper::kInvokeResponseFieldNumber:
      return absl::InternalError("received InvokeResponse instead of GetPublicKeyResponse");
    case ResponseWrapper::RESPONSE_NOT_SET:
    default:
      return absl::InternalError("received unsupported response: " + response->DebugString());
  }
}

absl::StatusOr<std::string> GrpcStreamingTransport::Invoke(absl::string_view request_bytes) {
  // Create request.
  RequestWrapper request;
  InvokeRequest* invoke_request = request.mutable_invoke_request();
  invoke_request->set_encrypted_body(request_bytes);

  // Send request.
  auto response = Send(request);
  if (!response.ok()) {
    return response.status();
  }

  // Process response.
  switch (response->response_case()) {
    case ResponseWrapper::kGetPublicKeyResponseFieldNumber:
      return absl::InternalError("received GetPublicKeyResponse instead of InvokeResponse");
    case ResponseWrapper::kInvokeResponseFieldNumber:
      return response->invoke_response().encrypted_body();
    case ResponseWrapper::RESPONSE_NOT_SET:
    default:
      return absl::InternalError("received unsupported response: " + response->DebugString());
  }
}

GrpcStreamingTransport::~GrpcStreamingTransport() {
  absl::Status status = Close();
  if (!status.ok()) {
    LOG(WARNING) << "couldn't stop gRPC stream: " << status.message();
  }
}

absl::StatusOr<ResponseWrapper> GrpcStreamingTransport::Send(const RequestWrapper& request) {
  // Send a request.
  if (!channel_reader_writer_->Write(request)) {
    return absl::InternalError("couldn't send request");
  }

  // Receive a response.
  ResponseWrapper response;
  if (!channel_reader_writer_->Read(&response)) {
    return absl::InternalError("couldn't receive response");
  }
  return response;
}

absl::Status GrpcStreamingTransport::Close() {
  if (!channel_reader_writer_->WritesDone()) {
    return absl::InternalError("couldn't close writing stream");
  }
  ::grpc::Status status = channel_reader_writer_->Finish();
  if (!status.ok()) {
    return absl::InternalError("couldn't close reading stream: " + status.error_message());
  }
  return absl::OkStatus();
}

}  // namespace oak::transport

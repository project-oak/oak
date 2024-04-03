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

#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/transport/util.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/grpcpp.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"

namespace oak::transport {

using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::session::v1::GetEndorsedEvidenceRequest;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;

absl::StatusOr<EndorsedEvidence> GrpcStreamingTransport::GetEndorsedEvidence() {
  // Create request.
  RequestWrapper request;
  GetEndorsedEvidenceRequest get_endorsed_evidence_request;
  *request.mutable_get_endorsed_evidence_request() =
      get_endorsed_evidence_request;

  // Send request.
  auto response = Send(request);
  if (!response.ok()) {
    return response.status();
  }

  // Process response.
  switch (response->response_case()) {
    case ResponseWrapper::kGetEndorsedEvidenceResponseFieldNumber:
      return response->get_endorsed_evidence_response().endorsed_evidence();
    case ResponseWrapper::kInvokeResponseFieldNumber:
      return absl::InternalError(
          "received InvokeResponse instead of GetEndorsedEvidenceResponse");
    case ResponseWrapper::RESPONSE_NOT_SET:
    default:
      return absl::InternalError("received unsupported response: " +
                                 absl::StrCat(*response));
  }
}

absl::StatusOr<EncryptedResponse> GrpcStreamingTransport::Invoke(
    const EncryptedRequest& encrypted_request) {
  // Create request.
  RequestWrapper request;
  *request.mutable_invoke_request()->mutable_encrypted_request() =
      encrypted_request;

  // Send request.
  auto response = Send(request);
  if (!response.ok()) {
    return response.status();
  }

  // Process response.
  switch (response->response_case()) {
    case ResponseWrapper::kGetEndorsedEvidenceResponseFieldNumber:
      return absl::InternalError(
          "received GetEndorsedEvidenceResponse instead of InvokeResponse");
    case ResponseWrapper::kInvokeResponseFieldNumber:
      return response->invoke_response().encrypted_response();
    case ResponseWrapper::RESPONSE_NOT_SET:
    default:
      return absl::InternalError("received unsupported response: " +
                                 absl::StrCat(*response));
  }
}

GrpcStreamingTransport::~GrpcStreamingTransport() {
  absl::Status status = Close();
  if (!status.ok()) {
    LOG(WARNING) << "couldn't stop gRPC stream: " << status.message();
  }
}

absl::StatusOr<ResponseWrapper> GrpcStreamingTransport::Send(
    const RequestWrapper& request) {
  // Send a request.
  if (!channel_reader_writer_->Write(request)) {
    absl::Status status = Close();
    if (status.ok()) {
      return absl::InternalError(
          "failed to read request for unspecified reason. This is likely an "
          "implementation bug.");
    } else {
      return absl::Status(status.code(), absl::StrCat("while writing request: ",
                                                      status.message()));
    }
  }

  // Receive a response.
  ResponseWrapper response;
  if (!channel_reader_writer_->Read(&response)) {
    absl::Status status = Close();
    if (status.ok()) {
      return absl::InternalError(
          "failed to write request for unspecified reason. This is likely an "
          "implementation bug.");
    } else {
      return absl::Status(status.code(), absl::StrCat("while reading request: ",
                                                      status.message()));
    }
  }
  return response;
}

absl::Status GrpcStreamingTransport::Close() {
  absl::call_once(close_once_, [this]() {
    channel_reader_writer_->WritesDone();
    grpc::Status grpc_close_status = channel_reader_writer_->Finish();
    close_status_ = to_absl_status(grpc_close_status);
  });
  return close_status_;
}

}  // namespace oak::transport

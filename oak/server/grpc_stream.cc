/*
 * Copyright 2018 The Project Oak Authors
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

#include "asylo/util/logging.h"

#include "oak/server/grpc_event.h"
#include "oak/server/grpc_stream.h"

namespace oak {
namespace grpc_server {

GrpcStream::GrpcStream(std::shared_ptr<::oak::grpc_server::OakNode> node_)
    : server_reader_writer_(&server_context_), node_(node_) {}

void GrpcStream::OnNewGrpc(bool ok) {
  // Read request data.
  server_reader_writer_.Read(&request_buffer_, new GrpcEvent(GrpcEvent::REQUEST_READ, this));
}

void GrpcStream::OnRequestRead(bool ok) {
  // Invoke the actual gRPC handler on the Oak Node.
  const grpc::GenericServerContext* x = &server_context_;
  ::grpc::Status status = node_->HandleGrpcCall(x, &request_buffer_, &response_buffer_);
  if (!status.ok()) {
    LOG(INFO) << "Failed: " << status.error_message();
  }

  ::grpc::WriteOptions options;

  // Write response data.
  server_reader_writer_.WriteAndFinish(response_buffer_, options, status,
                                       new GrpcEvent(GrpcEvent::RESPONSE_WRITTEN, this));
}

void GrpcStream::OnResponseWritten(bool ok) {
  // Ignore for now.
}

}  // namespace grpc_server
}  // namespace oak
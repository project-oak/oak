/*
 * Copyright 2019 The Project Oak Authors
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

#ifndef OAK_GRPC_SERVER_GRPC_STREAM_H_
#define OAK_GRPC_SERVER_GRPC_STREAM_H_

#include "include/grpcpp/generic/async_generic_service.h"
#include "include/grpcpp/impl/codegen/service_type.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"

#include "oak/server/grpc_stream.h"
#include "oak/server/oak_node.h"

namespace oak {
namespace grpc_server {

// gRPC stream state, needed to process requests.
class GrpcStream {
 public:
  GrpcStream(std::shared_ptr<OakNode> node_)
      : server_reader_writer_(&server_context_), node_(node_) {}

  void HandleCreateStream() {
    LOG(INFO) << "gRPC Event: New stream created";
    auto callback = new std::function<void()>([this]() { HandleReadEvent(); });
    server_reader_writer_.Read(&request_buffer_, callback);
  }

  grpc::GenericServerContext& server_context() { return server_context_; }
  grpc::GenericServerAsyncReaderWriter& server_reader_writer() { return server_reader_writer_; }

 private:
  void HandleReadEvent() {
    LOG(INFO) << "gRPC Event: Completed reading request";
    // Invoke the actual gRPC handler on the Oak Node.
    ::grpc::Status status =
        node_->HandleGrpcCall(&server_context_, &request_buffer_, &response_buffer_);
    if (!status.ok()) {
      LOG(WARNING) << "Failed: " << status.error_message();
    }

    ::grpc::WriteOptions options;

    // Write response data.
    auto callback = new std::function<void()>([this]() { HandleWriteEvent(); });
    server_reader_writer_.WriteAndFinish(response_buffer_, options, status, callback);
  }

  void HandleWriteEvent() { LOG(INFO) << "gRPC Event: Completed writing response"; }

  grpc::GenericServerContext server_context_;
  grpc::GenericServerAsyncReaderWriter server_reader_writer_;
  grpc::ByteBuffer request_buffer_;
  grpc::ByteBuffer response_buffer_;
  std::shared_ptr<OakNode> node_;
};

}  // namespace grpc_server
}  // namespace oak

#endif  // OAK_GRPC_SERVER_GRPC_STREAM_H_

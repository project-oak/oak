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

  grpc::GenericServerContext& server_context() { return server_context_; }
  grpc::GenericServerAsyncReaderWriter& server_reader_writer() { return server_reader_writer_; }
  grpc::ByteBuffer& request_buffer() { return request_buffer_; }
  grpc::ByteBuffer& response_buffer() { return response_buffer_; }
  std::shared_ptr<OakNode> node() { return node_; }

 private:
  grpc::GenericServerContext server_context_;
  grpc::GenericServerAsyncReaderWriter server_reader_writer_;
  grpc::ByteBuffer request_buffer_;
  grpc::ByteBuffer response_buffer_;
  std::shared_ptr<OakNode> node_;
};
}  // namespace grpc_server
}  // namespace oak

#endif  // OAK_GRPC_SERVER_GRPC_STREAM_H_

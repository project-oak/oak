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

#ifndef OAK_SERVER_MODULE_INVOCATION_H_
#define OAK_SERVER_MODULE_INVOCATION_H_

#include <memory>

#include "include/grpcpp/generic/async_generic_service.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/server/channel.h"
#include "oak/server/oak_grpc_node.h"

namespace oak {

// ModuleInvocation encapsulates the state necessary to process gRPC requests for
// an Oak Module invocation and execute them in the Oak VM.
class ModuleInvocation {
 public:
  // All constructor arguments must outlive this object.  It manages its own
  // lifetime after RequestNext is called.
  ModuleInvocation(grpc::AsyncGenericService* service, grpc::ServerCompletionQueue* queue,
                   OakGrpcNode* grpc_node)
      : service_(service),
        queue_(queue),
        grpc_node_(grpc_node),
        stream_(&context_),
        stream_id_(grpc_node_->NextStreamID()) {}

  // This object deletes itself.
  ~ModuleInvocation() = default;

  // Starts the asynchronous gRPC flow, which calls ReadRequest when the next
  // Oak Module invocation request arrives.
  // Must be called once.
  void Start();

  // Calls ProcessRequest after asynchronously reading the request.
  void ReadRequest(bool ok);

  // Performs the Oak Module invocation synchronously and calls SendResponse for
  // responses.  (On invocation failure, calls Finish and re-Start()s the gRPC
  // flow with a new ModuleInvocation object for the next request.
  void ProcessRequest(bool ok);

  // Sends a single response and queues an invocation of either:
  //  - SendResponse again if more responses are pending
  //  - Finish otherwise (and also re-Start()s the gRPC flow with a new
  //    ModuleInvocation object).
  void SendResponse(bool ok);
  void BlockingSendResponse();

  // Cleans up by deleting this object.
  void CleanUp(bool ok);

 private:
  void FinishAndCleanUp(const grpc::Status& status);

  grpc::AsyncGenericService* const service_;
  grpc::ServerCompletionQueue* const queue_;

  // Borrowed references to gRPC Node that this invocation is on behalf of.
  OakGrpcNode* grpc_node_;

  std::unique_ptr<MessageChannelReadHalf> rsp_half_;

  grpc::GenericServerContext context_;
  grpc::GenericServerAsyncReaderWriter stream_;
  grpc::ByteBuffer request_;

  const int32_t stream_id_;
};

}  // namespace oak

#endif  // OAK_SERVER_MODULE_INVOCATION_H_

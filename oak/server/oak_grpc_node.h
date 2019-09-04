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

#ifndef OAK_SERVER_OAK_GRPC_NODE_H_
#define OAK_SERVER_OAK_GRPC_NODE_H_

#include "include/grpcpp/grpcpp.h"
#include "oak/proto/application.grpc.pb.h"
#include "oak/server/channel.h"

namespace oak {

class OakGrpcNode final : public Application::Service {
 public:
  static std::unique_ptr<OakGrpcNode> Create();
  grpc::Status Start();
  grpc::Status Stop();

  void SetUpGrpcChannels(std::shared_ptr<MessageChannel> grpc_in,
                         std::shared_ptr<MessageChannel> grpc_out);

  int GetPort() { return port_; };
  // The destructor for a running OakGrpcNode instance will block until the thread
  // running the instance completes.
  virtual ~OakGrpcNode(){};

 private:
  OakGrpcNode() = default;
  OakGrpcNode(const OakGrpcNode&) = delete;
  OakGrpcNode& operator=(const OakGrpcNode&) = delete;

  int port_;

  grpc::Status GetAttestation(grpc::ServerContext* context, const GetAttestationRequest* request,
                              GetAttestationResponse* response) override;

  // Consumes gRPC events from the completion queue in an infinite loop.
  void CompletionQueueLoop();

  // gRPC async service and completion queue.
  // TODO: remove this once we have a unify way to pass channels around
  std::shared_ptr<MessageChannel> grpc_in_;
  std::shared_ptr<MessageChannel> grpc_out_;

  std::unique_ptr<::grpc::Server> server_;

  std::unique_ptr<grpc::AsyncGenericService> module_service_;
  // The queue expects to deal with void* tag values that are always function pointers to
  // void(bool) functions.
  std::unique_ptr<grpc::ServerCompletionQueue> completion_queue_;
};

}  // namespace oak

#endif  // OAK_SERVER_OAK_GRPC_NODE_H_

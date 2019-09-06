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

#include "oak/server/oak_grpc_node.h"
#include "absl/memory/memory.h"
#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/util/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/server/module_invocation.h"

namespace oak {

std::unique_ptr<OakGrpcNode> OakGrpcNode::Create() {
  std::unique_ptr<OakGrpcNode> node = absl::WrapUnique(new OakGrpcNode());
  node->grpc_in_ = std::make_shared<MessageChannel>();
  node->grpc_out_ = std::make_shared<MessageChannel>();

  // Build Server
  grpc::ServerBuilder builder;

  // Use ":0" notation so that server listens on a free port.
  builder.AddListeningPort(
      "[::]:0", asylo::EnclaveServerCredentials(asylo::BidirectionalNullCredentialsOptions()),
      &node->port_);
  builder.RegisterService(node.get());

  // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak Node.
  node->completion_queue_ = builder.AddCompletionQueue();

  // Register an async service.
  node->module_service_ = absl::make_unique<grpc::AsyncGenericService>();
  builder.RegisterAsyncGenericService(node->module_service_.get());

  node->server_ = builder.BuildAndStart();
  if (!node->server_) {
    LOG(QFATAL) << "Failed to start gRPC server";
    return nullptr;
  }

  return node;
}

grpc::Status OakGrpcNode::Start() {
  // Start a new thread to process the gRPC completion queue.
  std::thread thread(&OakGrpcNode::CompletionQueueLoop, this);
  thread.detach();
  // TODO: This thread will need to be joined once we sort out termination.
  return grpc::Status::OK;
}

void OakGrpcNode::CompletionQueueLoop() {
  LOG(INFO) << "Starting gRPC completion queue loop";
  // The stream object will delete itself when finished with the request,
  // after creating a new stream object for the next request.
  auto stream =
      new ModuleInvocation(module_service_.get(), completion_queue_.get(), grpc_in_, grpc_out_);
  stream->Start();
  while (true) {
    bool ok;
    void* tag;
    if (!completion_queue_->Next(&tag, &ok)) {
      LOG(FATAL) << "Failure reading from completion queue";
      return;
    }
    auto callback = static_cast<std::function<void(bool)>*>(tag);
    (*callback)(ok);
    delete callback;
  }
}

void OakGrpcNode::AddReadChannel(std::shared_ptr<MessageChannel> grpc_out) {
  grpc_out_ = grpc_out;
}
void OakGrpcNode::AddWriteChannel(std::shared_ptr<MessageChannel> grpc_in) {
  grpc_in_ = grpc_in;
}

grpc::Status OakGrpcNode::GetAttestation(grpc::ServerContext* context,
                                         const GetAttestationRequest* request,
                                         GetAttestationResponse* response) {
  // TODO: Move this method to the application and implement it there.
  return ::grpc::Status::OK;
}

grpc::Status OakGrpcNode::Stop() {
  if (server_) {
    LOG(INFO) << "Shutting down...";
    server_->Shutdown();
    server_ = nullptr;
  }
  return grpc::Status::OK;
}

}  // namespace oak

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
#include "include/grpcpp/grpcpp.h"
#include "oak/common/app_config.h"
#include "oak/common/logging.h"
#include "oak/server/module_invocation.h"

namespace oak {

std::unique_ptr<OakGrpcNode> OakGrpcNode::Create(BaseRuntime* runtime, const std::string& name,
                                                 const uint16_t port) {
  std::unique_ptr<OakGrpcNode> node = absl::WrapUnique(new OakGrpcNode(runtime, name));

  // Build Server
  grpc::ServerBuilder builder;

  // The default value is "[::]:0", that is used to listen on a free port.
  std::stringstream address;
  address << "[::]:" << port;
  builder.AddListeningPort(
      address.str(), asylo::EnclaveServerCredentials(asylo::BidirectionalNullCredentialsOptions()),
      &node->port_);

  // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak Node.
  node->completion_queue_ = builder.AddCompletionQueue();

  // Register an async service.
  node->module_service_ = absl::make_unique<grpc::AsyncGenericService>();
  builder.RegisterAsyncGenericService(node->module_service_.get());

  node->server_ = builder.BuildAndStart();
  if (!node->server_) {
    OAK_LOG(FATAL) << "Failed to start gRPC server";
    return nullptr;
  }

  return node;
}

void OakGrpcNode::Start() {
  // Start a new thread to process the gRPC completion queue.
  queue_thread_ = std::thread(&OakGrpcNode::CompletionQueueLoop, this);
}

void OakGrpcNode::CompletionQueueLoop() {
  OAK_LOG(INFO) << "{" << name_ << "} Starting gRPC completion queue loop";

  // The stream object will delete itself when finished with the request,
  // after creating a new stream object for the next request.
  auto stream = new ModuleInvocation(module_service_.get(), completion_queue_.get(), this);
  stream->Start();
  while (true) {
    bool ok;
    void* tag;
    if (!completion_queue_->Next(&tag, &ok)) {
      if (!runtime_->TerminationPending()) {
        OAK_LOG(FATAL) << "{" << name_ << "} Failure reading from completion queue";
      }
      OAK_LOG(INFO) << "{" << name_
                    << "} No Next event on completion queue, stopping gRPC completion queue loop";
      return;
    }
    auto callback = static_cast<std::function<void(bool)>*>(tag);
    (*callback)(ok);
    delete callback;
  }
}

void OakGrpcNode::Stop() {
  if (server_) {
    OAK_LOG(INFO) << "{" << name_ << "} Shutting down gRPC server...";
    server_->Shutdown();
  }
  if (completion_queue_ != nullptr) {
    OAK_LOG(INFO) << "{" << name_ << "} Shutting down completion queue...";
    completion_queue_->Shutdown();
  }
  if (queue_thread_.joinable()) {
    OAK_LOG(INFO) << "{" << name_ << "} Waiting for completion of completion queue thread";
    queue_thread_.join();
    OAK_LOG(INFO) << "{" << name_ << "} Completed queue thread";
  }
  // Now there is no separate thread running it's safe to drop the gRPC objects.
  server_ = nullptr;
  completion_queue_ = nullptr;
}

}  // namespace oak

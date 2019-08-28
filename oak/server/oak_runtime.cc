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

#include "oak/server/oak_runtime.h"

#include <functional>
#include <memory>
#include <string>
#include <thread>

#include "asylo/util/logging.h"
#include "asylo/util/status_macros.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/server/module_invocation.h"
#include "oak/server/oak_node.h"

namespace oak {

asylo::Status OakRuntime::InitializeServer(
    const ApplicationConfiguration& config,
    const std::shared_ptr<grpc::ServerCredentials> credentials) {
  LOG(INFO) << "Initializing Oak Application";
  if (config.nodes_size() != 1) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only application configurations with 1 Node are currently supported");
  }
  if (config.channels_size() != 0) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only application configurations with 0 Channels are currently supported");
  }
  const Node& node_configuration = config.nodes(0);
  if (!node_configuration.has_web_assembly_node()) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only WebAssembly Nodes are currently supported");
  }
  // TODO: Support creating multiple Nodes and Channels connecting them.
  const WebAssemblyNode& web_assembly_node = node_configuration.web_assembly_node();
  node_ = OakNode::Create(web_assembly_node.module_bytes());
  if (node_ == nullptr) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to create Oak Node");
  }

  SetUpChannels();

  // Ensure that the server is only created and initialized once.
  if (server_) {
    return asylo::Status::OkStatus();
  }

  ASYLO_ASSIGN_OR_RETURN(server_, CreateServer(credentials));

  // Start a new thread to process the gRPC completion queue.
  std::thread thread(&OakRuntime::CompletionQueueLoop, this);
  thread.detach();

  return asylo::Status::OkStatus();
}

asylo::StatusOr<std::unique_ptr<grpc::Server>> OakRuntime::CreateServer(
    const std::shared_ptr<grpc::ServerCredentials> credentials) {
  grpc::ServerBuilder builder;
  // Uses ":0" notation so that server listens on a free port.
  builder.AddListeningPort("[::]:0", credentials, &port_);
  builder.RegisterService(node_.get());

  // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak
  // Node.
  completion_queue_ = builder.AddCompletionQueue();
  builder.RegisterAsyncGenericService(&module_service_);

  std::unique_ptr<grpc::Server> server = builder.BuildAndStart();
  if (!server) {
    return asylo::Status(asylo::error::GoogleError::INTERNAL, "Failed to start gRPC server");
  }

  LOG(INFO) << "gRPC server is listening on port: " << port_;

  return std::move(server);
}

// Create all the necessary channels and pass the appropriate halves to |node_|.
void OakRuntime::SetUpChannels() {
  // Create a logging channel for the node.
  {
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node_->SetChannel(ChannelHandle::LOGGING, absl::make_unique<MessageChannelWriteHalf>(channel));
    LOG(INFO) << "Created logging channel " << ChannelHandle::LOGGING;

    // Spawn a thread that reads and logs messages on this channel forever.
    std::thread t([channel] {
      std::unique_ptr<MessageChannelReadHalf> read_chan =
          absl::make_unique<MessageChannelReadHalf>(channel);
      while (true) {
        ReadResult result = read_chan->BlockingRead(INT_MAX);
        if (result.required_size > 0) {
          LOG(ERROR) << "Message size too large: " << result.required_size;
          return;
        }
        LOG(INFO) << "LOG: " << std::string(result.data->data(), result.data->size());
      }
    });
    // TODO: join() instead when we have node termination
    t.detach();
  }

  // TODO: Set up remaining channels here rather than in OakNode.
}

int OakRuntime::GetServerAddress() { return port_; }

void OakRuntime::FinalizeServer() {
  if (server_) {
    LOG(INFO) << "Shutting down...";
    server_->Shutdown();
    server_ = nullptr;
  }
}

void OakRuntime::CompletionQueueLoop() {
  LOG(INFO) << "Starting gRPC completion queue loop";
  // The stream object will delete itself when finished with the request,
  // after creating a new stream object for the next request.
  auto* stream = new ModuleInvocation(&module_service_, completion_queue_.get(), node_.get());
  stream->Start();
  while (true) {
    bool ok;
    void* tag;
    if (!completion_queue_->Next(&tag, &ok)) {
      LOG(FATAL) << "Failure reading from completion queue";
      return;
    }
    auto* callback = static_cast<std::function<void(bool)>*>(tag);
    (*callback)(ok);
    delete callback;
  }
}

}  // namespace oak

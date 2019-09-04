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
#include "oak/server/module_invocation.h"
#include "oak/server/oak_node.h"

namespace oak {

asylo::Status OakRuntime::Initialize(const ApplicationConfiguration& config) {
  LOG(INFO) << "Initializing Oak Runtime";
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

  return asylo::Status::OkStatus();
}
grpc::Service* OakRuntime::GetGrpcService() { return node_.get(); }

asylo::Status OakRuntime::StartCompletionQueue(std::unique_ptr<grpc::AsyncGenericService> service,
                                               std::unique_ptr<grpc::ServerCompletionQueue> queue) {
  // Use the serivce and queue provided.
  // TODO: check to see if we already started this.
  module_service_ = std::move(service);
  completion_queue_ = std::move(queue);

  // Start the logging pseudo-node thread.
  logging_node_->Start();

  // Start a new thread to process the gRPC completion queue.
  std::thread thread(&OakRuntime::CompletionQueueLoop, this);
  thread.detach();

  // Start a new thread to process storage requests.
  storage_node_->Start();

  // Now all dependencies are running, start the thread for the Node itself.
  node_->Start();

  return asylo::Status::OkStatus();
}

void OakRuntime::SetUpChannels() {
  // Create logging channel and pass the read half to a new logging pseudo-node.
  auto logging_channel = std::make_shared<MessageChannel>();
  node_->SetChannel(ChannelHandle::LOGGING,
                    absl::make_unique<MessageChannelWriteHalf>(logging_channel));
  logging_node_ =
      absl::make_unique<LoggingNode>(absl::make_unique<MessageChannelReadHalf>(logging_channel));
  LOG(INFO) << "Created logging channel " << ChannelHandle::LOGGING << " and pseudo-node";

  // Create the channels needed for gRPC interactions.

  // Incoming request channel: keep the write half in |OakRuntime|, but map
  // the read half to a well-known channel handle on |node_|.
  grpc_in_ = std::make_shared<MessageChannel>();
  node_->SetChannel(ChannelHandle::GRPC_IN, absl::make_unique<MessageChannelReadHalf>(grpc_in_));
  LOG(INFO) << "Created gRPC input channel: " << ChannelHandle::GRPC_IN;

  // Outgoing response channel: keep the read half in |OakRuntime|, but map
  // the write half to a well-known channel handle on |node_|.
  grpc_out_ = std::make_shared<MessageChannel>();
  node_->SetChannel(ChannelHandle::GRPC_OUT, absl::make_unique<MessageChannelWriteHalf>(grpc_out_));
  LOG(INFO) << "Created gRPC output channel: " << ChannelHandle::GRPC_IN;

  // Create the channels needed for interaction with storage.

  // Outgoing storage request channel: keep the read half in C++, but map the write
  // half to a well-known channel handle.
  auto storage_req_channel = std::make_shared<MessageChannel>();
  node_->SetChannel(ChannelHandle::STORAGE_OUT,
                    absl::make_unique<MessageChannelWriteHalf>(storage_req_channel));
  auto storage_req_half = absl::make_unique<MessageChannelReadHalf>(storage_req_channel);
  LOG(INFO) << "Created storage output channel: " << ChannelHandle::STORAGE_OUT;

  // Inbound storage response channel: keep the write half in C++, but map the read
  // half to a well-known channel handle.
  auto storage_rsp_channel = std::make_shared<MessageChannel>();
  node_->SetChannel(ChannelHandle::STORAGE_IN,
                    absl::make_unique<MessageChannelReadHalf>(storage_rsp_channel));
  auto storage_rsp_half = absl::make_unique<MessageChannelWriteHalf>(storage_rsp_channel);
  LOG(INFO) << "Created storage input channel: " << ChannelHandle::STORAGE_IN;

  // Add in a storage pseudo-node.
  storage_node_ =
      absl::make_unique<StorageNode>(std::move(storage_req_half), std::move(storage_rsp_half));

  LOG(INFO) << "Created storage channels";
}

void OakRuntime::CompletionQueueLoop() {
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

}  // namespace oak

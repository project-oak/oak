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
#include "oak/server/storage/storage_read_channel.h"
#include "oak/server/storage/storage_write_channel.h"

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

  // Start a new thread to process the gRPC completion queue.
  std::thread thread(&OakRuntime::CompletionQueueLoop, this);
  thread.detach();

  node_->Start();

  return asylo::Status::OkStatus();
}

void OakRuntime::SetUpChannels() {
  // Create logging channel.
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

  node_->SetChannel(ChannelHandle::STORAGE_IN,
                    absl::make_unique<StorageReadChannel>(&storage_manager_));
  node_->SetChannel(ChannelHandle::STORAGE_OUT,
                    absl::make_unique<StorageWriteChannel>(&storage_manager_));
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

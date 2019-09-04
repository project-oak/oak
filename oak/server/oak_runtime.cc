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
  auto node = OakNode::Create(web_assembly_node.module_bytes());
  if (node == nullptr) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to create Oak Node");
  }

  // Setup the default channels for the node.
  SetUpChannels(*node.get());

  // TODO: This needs to be configurable
  // Create the pseudo node required.
  grpc_node_ = OakGrpcNode::Create();
  SetUpGrpcChannels(*node.get());

  // Move ownership to vector.
  wasm_nodes_.push_back(std::move(node));

  return asylo::Status::OkStatus();
}

asylo::Status OakRuntime::Start() {
  LOG(INFO) << "Starting runtime";

  // Start the gRPC pseudo-node.
  grpc_node_->Start();

  // Start the logging pseudo-node thread.
  logging_node_->Start();

  // Start a new thread to process storage requests.
  storage_node_->Start();

  // Now all dependencies are running, start the thread for the Node itself.
  for (auto& node : wasm_nodes_) {
    node->Start();
  }

  return asylo::Status::OkStatus();
}

// Create the default set of channels for given node. For now, this means logging and storage
// TODO: There probably shouldn't be any default list, as all these should come from the config.
void OakRuntime::SetUpChannels(OakNode& node) {
  // Create logging channel and pass the read half to a new logging pseudo-node.
  auto logging_channel = std::make_shared<MessageChannel>();
  node.SetChannel(ChannelHandle::LOGGING,
                  absl::make_unique<MessageChannelWriteHalf>(logging_channel));
  logging_node_ =
      absl::make_unique<LoggingNode>(absl::make_unique<MessageChannelReadHalf>(logging_channel));
  LOG(INFO) << "Created logging channel " << ChannelHandle::LOGGING << " and pseudo-node";

  // Create the channels needed for interaction with storage.

  // Outgoing storage request channel: keep the read half in C++, but map the write
  // half to a well-known channel handle.
  auto storage_req_channel = std::make_shared<MessageChannel>();
  node.SetChannel(ChannelHandle::STORAGE_OUT,
                  absl::make_unique<MessageChannelWriteHalf>(storage_req_channel));
  auto storage_req_half = absl::make_unique<MessageChannelReadHalf>(storage_req_channel);
  LOG(INFO) << "Created storage output channel: " << ChannelHandle::STORAGE_OUT;

  // Inbound storage response channel: keep the write half in C++, but map the read
  // half to a well-known channel handle.
  auto storage_rsp_channel = std::make_shared<MessageChannel>();
  node.SetChannel(ChannelHandle::STORAGE_IN,
                  absl::make_unique<MessageChannelReadHalf>(storage_rsp_channel));
  auto storage_rsp_half = absl::make_unique<MessageChannelWriteHalf>(storage_rsp_channel);
  LOG(INFO) << "Created storage input channel: " << ChannelHandle::STORAGE_IN;

  // Add in a storage pseudo-node.
  storage_node_ =
      absl::make_unique<StorageNode>(std::move(storage_req_half), std::move(storage_rsp_half));

  LOG(INFO) << "Created storage channels";
}

// Create the channels needed for gRPC interactions.
void OakRuntime::SetUpGrpcChannels(OakNode& node) {
  // Incoming request channel: keep the write half in |OakRuntime|, but map
  // the read half to a well-known channel handle on |node_|.
  grpc_in_ = std::make_shared<MessageChannel>();
  node.SetChannel(ChannelHandle::GRPC_IN, absl::make_unique<MessageChannelReadHalf>(grpc_in_));
  LOG(INFO) << "Created gRPC input channel: " << ChannelHandle::GRPC_IN;

  // Outgoing response channel: keep the read half in |OakRuntime|, but map
  // the write half to a well-known channel handle on |node_|.
  grpc_out_ = std::make_shared<MessageChannel>();
  node.SetChannel(ChannelHandle::GRPC_OUT, absl::make_unique<MessageChannelWriteHalf>(grpc_out_));
  LOG(INFO) << "Created gRPC output channel: " << ChannelHandle::GRPC_IN;

  grpc_node_->SetUpGrpcChannels(grpc_in_, grpc_out_);
}

int32_t OakRuntime::GetPort() { return grpc_node_->GetPort(); }

asylo::Status OakRuntime::Stop() {
  LOG(INFO) << "Stopping runtime...";
  for (auto& node : wasm_nodes_) {
    node->Stop();
  }
  wasm_nodes_.clear();

  // TODO: make grpc_node_ generic
  if (grpc_node_) {
    grpc_node_->Stop();
    grpc_node_ = nullptr;
  }

  return asylo::Status::OkStatus();
}

}  // namespace oak

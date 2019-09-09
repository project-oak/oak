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
#include "oak/common/app_config.h"
#include "oak/server/module_invocation.h"
#include "oak/server/oak_node.h"

namespace oak {

asylo::Status OakRuntime::Initialize(const ApplicationConfiguration& config) {
  LOG(INFO) << "Initializing Oak Runtime";
  if (!ValidApplicationConfig(config)) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Invalid configuration");
  }

  // TODO: Support creating multiple Nodes and Channels connecting them.

  // Find first (only) Wasm node in the config (which must exist, because of
  // the validity check above).
  std::unique_ptr<OakNode> node = nullptr;
  for (const auto& node_config : config.nodes()) {
    if (node_config.has_web_assembly_node()) {
      node =
          OakNode::Create(node_config.node_name(), node_config.web_assembly_node().module_bytes());
      break;
    }
  }
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
  Handle log_handle =
      node.AddNamedChannel("log", absl::make_unique<MessageChannelWriteHalf>(logging_channel));
  logging_node_ = absl::make_unique<LoggingNode>();
  logging_node_->AddChannel(absl::make_unique<MessageChannelReadHalf>(logging_channel));
  LOG(INFO) << "Created logging channel " << log_handle << " and pseudo-node";

  // Create the channels needed for interaction with storage.

  // Outgoing storage request channel: keep the read half in C++, but map the write
  // half to a well-known channel handle.
  auto storage_req_channel = std::make_shared<MessageChannel>();
  Handle storage_out_handle = node.AddNamedChannel(
      "storage_out", absl::make_unique<MessageChannelWriteHalf>(storage_req_channel));
  auto storage_req_half = absl::make_unique<MessageChannelReadHalf>(storage_req_channel);
  LOG(INFO) << "Created storage output channel: " << storage_out_handle;

  // Inbound storage response channel: keep the write half in C++, but map the read
  // half to a well-known channel handle.
  auto storage_rsp_channel = std::make_shared<MessageChannel>();
  Handle storage_in_handle = node.AddNamedChannel(
      "storage_in", absl::make_unique<MessageChannelReadHalf>(storage_rsp_channel));
  auto storage_rsp_half = absl::make_unique<MessageChannelWriteHalf>(storage_rsp_channel);
  LOG(INFO) << "Created storage input channel: " << storage_in_handle;

  // Add in a storage pseudo-node.
  storage_node_ = absl::make_unique<StorageNode>("localhost:7867");
  storage_node_->AddReadChannel(std::move(storage_req_half));
  storage_node_->AddWriteChannel(std::move(storage_rsp_half));

  LOG(INFO) << "Created storage channels";
}

// Create the channels needed for gRPC interactions.
void OakRuntime::SetUpGrpcChannels(OakNode& node) {
  // Incoming request channel: keep the write half in |OakRuntime|, but map
  // the read half to a well-known channel handle on |node_|.
  auto grpc_in = std::make_shared<MessageChannel>();
  Handle grpc_in_handle =
      node.AddNamedChannel("grpc_in", absl::make_unique<MessageChannelReadHalf>(grpc_in));
  auto grpc_req_half = absl::make_unique<MessageChannelWriteHalf>(grpc_in);
  LOG(INFO) << "Created gRPC input channel: " << grpc_in_handle;

  // Outgoing response channel: keep the read half in |OakRuntime|, but map
  // the write half to a well-known channel handle on |node_|.
  auto grpc_out = std::make_shared<MessageChannel>();
  Handle grpc_out_handle =
      node.AddNamedChannel("grpc_out", absl::make_unique<MessageChannelWriteHalf>(grpc_out));
  auto grpc_rsp_half = absl::make_unique<MessageChannelReadHalf>(grpc_out);
  LOG(INFO) << "Created gRPC output channel: " << grpc_out_handle;

  grpc_node_->AddReadChannel(std::move(grpc_rsp_half));
  grpc_node_->AddWriteChannel(std::move(grpc_req_half));
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

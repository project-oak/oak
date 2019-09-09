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

namespace oak {

asylo::Status OakRuntime::Initialize(const ApplicationConfiguration& config) {
  LOG(INFO) << "Initializing Oak Runtime";
  if (!ValidApplicationConfig(config)) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Invalid configuration");
  }

  // Create all of the nodes.  The validity check above will ensure there
  // is at most one of each pseudo-Node type.
  std::string grpc_name;
  std::string logging_name;
  std::string storage_name;
  for (const auto& node_config : config.nodes()) {
    if (node_config.has_web_assembly_node()) {
      LOG(INFO) << "Create Wasm node named " << node_config.node_name();
      std::unique_ptr<WasmNode> node =
          WasmNode::Create(node_config.node_name(), node_config.web_assembly_node().module_bytes());
      if (node == nullptr) {
        return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                             "Failed to create Oak Node");
      }
      wasm_nodes_[node_config.node_name()] = std::move(node);
    } else if (node_config.has_grpc_server_node()) {
      grpc_name = node_config.node_name();
      LOG(INFO) << "Create gRPC pseudo-Node named " << grpc_name;
      grpc_node_ = OakGrpcNode::Create();
    } else if (node_config.has_log_node()) {
      logging_name = node_config.node_name();
      LOG(INFO) << "Create logging pseudo-node named " << logging_name;
      logging_node_ = absl::make_unique<LoggingNode>();
    } else if (node_config.has_storage_node()) {
      storage_name = node_config.node_name();
      LOG(INFO) << "Created storage pseudo-Node named " << storage_name;
      storage_node_ = absl::make_unique<StorageNode>(node_config.storage_node().address());
    }
  }

  // Now create channels.
  for (const auto& channel_config : config.channels()) {
    const std::string& src_node = channel_config.source_endpoint().node_name();
    const std::string& src_port = channel_config.source_endpoint().port_name();
    const std::string& dest_node = channel_config.destination_endpoint().node_name();
    const std::string& dest_port = channel_config.destination_endpoint().port_name();

    LOG(INFO) << "Create channel " << src_node << "." << src_port << " -> " << dest_node << "."
              << dest_port;
    auto channel = std::make_shared<MessageChannel>();
    auto write_half = absl::make_unique<MessageChannelWriteHalf>(channel);
    auto read_half = absl::make_unique<MessageChannelReadHalf>(channel);

    // TODO: Make pseudo-node channel setup less of a special case.

    // Wire up the source endpoint.
    if (wasm_nodes_.count(src_node) == 1) {
      wasm_nodes_[src_node]->AddNamedChannel(src_port, std::move(write_half));
    } else if (src_node == grpc_name) {
      grpc_node_->AddWriteChannel(std::move(write_half));
    } else if (src_node == storage_name) {
      storage_node_->AddWriteChannel(std::move(write_half));
    } else {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                           "Channel with unknown source node");
    }

    // Wire up the destination endpoint
    if (wasm_nodes_.count(dest_node) == 1) {
      wasm_nodes_[dest_node]->AddNamedChannel(dest_port, std::move(read_half));
    } else if (dest_node == grpc_name) {
      grpc_node_->AddReadChannel(std::move(read_half));
    } else if (dest_node == storage_name) {
      storage_node_->AddReadChannel(std::move(read_half));
    } else if (dest_node == logging_name) {
      logging_node_->AddChannel(std::move(read_half));
    } else {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                           "Channel with unknown destination node");
    }
  }

  return asylo::Status::OkStatus();
}

asylo::Status OakRuntime::Start() {
  LOG(INFO) << "Starting runtime";

  // Start the gRPC pseudo-node.
  if (grpc_node_ != nullptr) {
    grpc_node_->Start();
  }

  // Start the logging pseudo-node thread.
  if (logging_node_ != nullptr) {
    logging_node_->Start();
  }

  // Start a new thread to process storage requests.
  if (storage_node_ != nullptr) {
    storage_node_->Start();
  }

  // Now all dependencies are running, start the thread for all the Wasm Nodes.
  for (auto& named_node : wasm_nodes_) {
    LOG(INFO) << "Starting Wasm node " << named_node.first;
    named_node.second->Start();
  }

  return asylo::Status::OkStatus();
}

int32_t OakRuntime::GetPort() { return grpc_node_->GetPort(); }

asylo::Status OakRuntime::Stop() {
  LOG(INFO) << "Stopping runtime...";
  for (auto& named_node : wasm_nodes_) {
    LOG(INFO) << "Stopping Wasm node " << named_node.first;
    named_node.second->Stop();
  }
  wasm_nodes_.clear();

  // TODO: make grpc_node_ generic
  if (grpc_node_) {
    grpc_node_->Stop();
    grpc_node_ = nullptr;
  }
  // TODO: stop other pseudo-Nodes if present

  return asylo::Status::OkStatus();
}

}  // namespace oak

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

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "oak/common/app_config.h"
#include "oak/server/rust/oak_runtime.h"
#include "oak/server/wasm_node.h"

namespace oak {

grpc::Status OakRuntime::Initialize(const ApplicationConfiguration& config) {
  LOG(INFO) << "Initializing Oak Runtime";
  if (!ValidApplicationConfig(config)) {
    return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Invalid configuration");
  }

  // Accumulate the name => module_bytes map.
  wasm_contents_.clear();
  for (const auto& contents : config.wasm_contents()) {
    wasm_contents_[contents.name()] = absl::make_unique<std::string>(contents.module_bytes());
  }

  // Create all of the nodes.  The validity check above will ensure there is at
  // most one of each pseudo-Node type.
  OakNode* log_node = nullptr;
  for (const auto& node_config : config.nodes()) {
    const std::string& node_name = node_config.node_name();
    std::unique_ptr<OakNode> node;
    if (node_config.has_web_assembly_node()) {
      const auto& wasm_node = node_config.web_assembly_node();
      LOG(INFO) << "Create Wasm node named {" << node_name << "}";
      const std::string* module_bytes = wasm_contents_[wasm_node.wasm_contents_name()].get();
      node = WasmNode::Create(this, node_config.node_name(), *module_bytes);
    } else if (node_config.has_grpc_server_node()) {
      LOG(INFO) << "Create gRPC pseudo-Node named {" << node_name << "}";
      std::unique_ptr<OakGrpcNode> grpc_node = OakGrpcNode::Create(node_name);
      grpc_node_ = grpc_node.get();  // borrowed copy
      node = std::move(grpc_node);
    } else if (node_config.has_log_node()) {
      LOG(INFO) << "Create logging pseudo-node named {" << node_name << "}";
      node = absl::make_unique<LoggingNode>(node_name);
      log_node = node.get();
    } else if (node_config.has_storage_node()) {
      LOG(INFO) << "Created storage pseudo-Node named {" << node_name << "}";
      node = absl::make_unique<StorageNode>(node_name, node_config.storage_node().address());
    }
    if (node == nullptr) {
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Failed to create Oak Node");
    }
    nodes_[node_name] = std::move(node);
  }

  // Now create channels.
  MessageChannelWriteHalf* logging_channel = nullptr;
  for (const auto& channel_config : config.channels()) {
    const std::string& src_name = channel_config.source_endpoint().node_name();
    const std::string& src_port = channel_config.source_endpoint().port_name();
    const std::string& dest_name = channel_config.destination_endpoint().node_name();
    const std::string& dest_port = channel_config.destination_endpoint().port_name();
    OakNode* src_node = nodes_[src_name].get();
    OakNode* dest_node = nodes_[dest_name].get();
    if (src_node == nullptr || dest_node == nullptr) {
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Node at end of channel not found");
    }

    if (dest_node == log_node && logging_channel != nullptr) {
      // Special case for all configured channels going to the logging
      // pseudo-Node: share the existing channel and hold an extra reference to
      // the write half of the channel.
      LOG(INFO) << "Re-use logging channel for {" << src_name << "}." << src_port << " -> {"
                << dest_name << "}." << dest_port;
      src_node->AddNamedChannel(src_port, absl::make_unique<ChannelHalf>(logging_channel->Clone()));
    } else {
      LOG(INFO) << "Create channel {" << src_name << "}." << src_port << " -> {" << dest_name
                << "}." << dest_port;
      MessageChannel::ChannelHalves halves = MessageChannel::Create();
      if (dest_node == log_node) {
        // Remember the write half of logging channel for future re-use.
        logging_channel = halves.write.get();
      }

      src_node->AddNamedChannel(src_port, absl::make_unique<ChannelHalf>(std::move(halves.write)));
      dest_node->AddNamedChannel(dest_port, absl::make_unique<ChannelHalf>(std::move(halves.read)));
    }
  }

  return grpc::Status::OK;
}

grpc::Status OakRuntime::Start() {
  // We call into the Rust runtime to verify that bindings between C++ and Rust are working
  // correctly.
  {
    LOG(INFO) << "Calling Rust runtime";
    int32_t rust_check = add_magic_number(1000);
    LOG(INFO) << "Rust runtime called, result: " << rust_check;
  }

  LOG(INFO) << "Starting runtime";

  // Now all dependencies are running, start the thread for all the Wasm Nodes.
  for (auto& named_node : nodes_) {
    LOG(INFO) << "Starting node " << named_node.first;
    named_node.second->Start();
  }

  return grpc::Status::OK;
}

int32_t OakRuntime::GetPort() { return grpc_node_->GetPort(); }

grpc::Status OakRuntime::Stop() {
  LOG(INFO) << "Stopping runtime...";
  grpc_node_ = nullptr;
  for (auto& named_node : nodes_) {
    LOG(INFO) << "Stopping node " << named_node.first;
    named_node.second->Stop();
  }
  nodes_.clear();

  return grpc::Status::OK;
}

}  // namespace oak

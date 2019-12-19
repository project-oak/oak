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
#include "absl/strings/str_cat.h"
#include "asylo/util/logging.h"
#include "oak/common/app_config.h"
#include "oak/server/rust/oak_runtime.h"
#include "oak/server/wasm_node.h"

namespace oak {

namespace {
// Name to use for the (sole) gRPC pseudo-Node.  This will not clash with any
// dynamically created Node names because they are all of the form
// "<config>-<number>".
constexpr char kGrpcNodeName[] = "grpc";
}  // namespace

grpc::Status OakRuntime::Initialize(const ApplicationConfiguration& config) {
  LOG(INFO) << "Initializing Oak Runtime";
  if (!ValidApplicationConfig(config)) {
    return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Invalid configuration");
  }
  absl::MutexLock lock(&mu_);

  // Accumulate the various data structures indexed by config name.
  wasm_config_.clear();
  log_config_.clear();
  storage_config_.clear();
  for (const auto& node_config : config.node_configs()) {
    if (node_config.has_wasm_config()) {
      const WebAssemblyConfiguration& wasm_config = node_config.wasm_config();
      wasm_config_[node_config.name()] = absl::make_unique<std::string>(wasm_config.module_bytes());
    } else if (node_config.has_log_config()) {
      log_config_.insert(node_config.name());
    } else if (node_config.has_storage_config()) {
      const StorageProxyConfiguration& storage_config = node_config.storage_config();
      storage_config_[node_config.name()] =
          absl::make_unique<std::string>(storage_config.address());
    }
  }

  // Create a gRPC pseudo-Node.
  const std::string grpc_name = kGrpcNodeName;
  LOG(INFO) << "Create gRPC pseudo-Node named {" << grpc_name << "}";
  std::unique_ptr<OakGrpcNode> grpc_node = OakGrpcNode::Create(grpc_name);
  grpc_node_ = grpc_node.get();  // borrowed copy
  nodes_[grpc_name] = std::move(grpc_node);

  // Create the initial Application Node.
  std::string node_name;
  OakNode* app_node = CreateNode(config.initial_node(), &node_name);
  if (app_node == nullptr) {
    return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Failed to create initial Oak Node");
  }
  LOG(INFO) << "Created Wasm node named {" << node_name << "}";

  // Create an initial channel from gRPC pseudo-Node to Application Node.
  // Both of the initial nodes have exactly one registered handle.
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  Handle grpc_handle =
      grpc_node_->AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.write)));
  Handle app_handle = app_node->AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.read)));
  LOG(INFO) << "Created initial channel from Wasm node {" << grpc_name << "}." << grpc_handle
            << " to {" << node_name << "}." << app_handle;

  return grpc::Status::OK;
}

std::string OakRuntime::NextNodeName(const std::string& config) {
  int index = next_index_[config]++;
  return absl::StrCat(config, "-", index);
}

// Create (but don't start) a new Node instance.  Return a borrowed pointer to
// the new Node (or nullptr on failure).
OakNode* OakRuntime::CreateNode(const std::string& config, std::string* /*node_name*/) {
  std::string name = NextNodeName(config);
  std::unique_ptr<OakNode> node;

  if (wasm_config_.count(config) > 0) {
    LOG(INFO) << "Create Wasm node named {" << name << "}";
    const std::string* module_bytes = wasm_config_[config].get();
    node = WasmNode::Create(this, name, *module_bytes);
  } else if (log_config_.count(config) > 0) {
    LOG(INFO) << "Create log node named {" << name << "}";
    node = absl::make_unique<LoggingNode>(name);
  } else if (storage_config_.count(config) > 0) {
    std::string address = *(storage_config_[config].get());
    LOG(INFO) << "Create storage proxy node named {" << name << "} connecting to " << address;
    node = absl::make_unique<StorageNode>(name, address);
  } else {
    LOG(ERROR) << "failed to find config with name " << config;
    return nullptr;
  }

  OakNode* result = node.get();
  if (node != nullptr) {
    nodes_[name] = std::move(node);
  } else {
    LOG(ERROR) << "failed to create Node with config of name " << config;
  }
  return result;
}

bool OakRuntime::CreateAndRunNode(const std::string& config, std::unique_ptr<ChannelHalf> half,
                                  std::string* node_name) {
  absl::MutexLock lock(&mu_);
  OakNode* node = CreateNode(config, node_name);
  if (node == nullptr) {
    return false;
  }

  // Add the given channel as the Node's single available handle.
  Handle handle = node->AddChannel(std::move(half));

  LOG(INFO) << "Start node named {" << *node_name << "} with initial handle " << handle;
  node->Start();
  return true;
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
  absl::MutexLock lock(&mu_);

  // Now all dependencies are running, start the Nodes running.
  for (auto& named_node : nodes_) {
    LOG(INFO) << "Starting node " << named_node.first;
    named_node.second->Start();
  }

  return grpc::Status::OK;
}

int32_t OakRuntime::GetPort() { return grpc_node_->GetPort(); }

grpc::Status OakRuntime::Stop() {
  LOG(INFO) << "Stopping runtime...";

  // Take local ownership of all the nodes owned by the runtime.
  std::map<std::string, std::unique_ptr<OakNode>> nodes;
  {
    absl::MutexLock lock(&mu_);
    grpc_node_ = nullptr;
    nodes = std::move(nodes_);
    nodes_.clear();
  }

  // Now stop all the nodes without holding the runtime lock, just
  // in case any of the per-Node threads happens to try an operation
  // (e.g. node_create) that needs the lock.
  for (auto& named_node : nodes) {
    LOG(INFO) << "Stopping node " << named_node.first;
    named_node.second->Stop();
  }

  return grpc::Status::OK;
}

}  // namespace oak

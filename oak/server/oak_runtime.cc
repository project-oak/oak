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
#include "oak/common/app_config.h"
#include "oak/common/logging.h"
#include "oak/server/grpc_client_node.h"
#include "oak/server/logging_node.h"
#include "oak/server/storage/storage_node.h"
#include "oak/server/wasm_node.h"

namespace oak {

namespace {
// Name to use for the (sole) gRPC pseudo-Node.  This will not clash with any
// dynamically created Node names because they are all of the form
// "<config>-<number>-<entrypoint>".
constexpr char kGrpcNodeName[] = "grpc";
}  // namespace

grpc::Status OakRuntime::Initialize(const ApplicationConfiguration& config,
                                    std::shared_ptr<grpc::ServerCredentials> grpc_credentials) {
  OAK_LOG(INFO) << "Initializing Oak Runtime";
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
      wasm_config_[node_config.name()] =
          absl::make_unique<const WebAssemblyConfiguration>(node_config.wasm_config());
    } else if (node_config.has_log_config()) {
      log_config_.insert(node_config.name());
    } else if (node_config.has_storage_config()) {
      const StorageProxyConfiguration& storage_config = node_config.storage_config();
      storage_config_[node_config.name()] =
          absl::make_unique<std::string>(storage_config.address());
    } else if (node_config.has_grpc_client_config()) {
      const GrpcClientConfiguration& grpc_config = node_config.grpc_client_config();
      grpc_client_config_[node_config.name()] =
          absl::make_unique<std::string>(grpc_config.address());
    }
  }

  // Create a gRPC pseudo-Node.
  NodeId grpc_node_id = NextNodeId();
  const std::string grpc_name = kGrpcNodeName;
  const uint16_t grpc_port = config.grpc_port();
  OAK_LOG(INFO) << "Create gRPC pseudo-Node named {" << grpc_name << "}";
  std::unique_ptr<OakGrpcNode> grpc_node =
      OakGrpcNode::Create(this, grpc_name, grpc_node_id, grpc_credentials, grpc_port);
  grpc_node_ = grpc_node.get();  // borrowed copy
  nodes_[grpc_name] = std::move(grpc_node);

  // Create the initial Application Node.
  NodeId app_node_id = NextNodeId();
  std::string node_name;
  app_node_ = CreateNode(config.initial_node_config_name(), config.initial_entrypoint_name(),
                         app_node_id, &node_name);
  if (app_node_ == nullptr) {
    return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Failed to create initial Oak Node");
  }
  OAK_LOG(INFO) << "Created Wasm node named {" << node_name << "}";

  // Create an initial channel from gRPC pseudo-Node to Application Node.
  // Both of the initial nodes have exactly one registered handle.
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  grpc_handle_ = grpc_node_->AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.write)));
  app_handle_ = app_node_->AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.read)));
  OAK_LOG(INFO) << "Created initial channel from Wasm node {" << grpc_name << "}." << grpc_handle_
                << " to {" << node_name << "}." << app_handle_;

  return grpc::Status::OK;
}

// Generate a unique (per-Runtime) name for a new Node, running the given Node
// configuration and entrypoint.
std::string OakRuntime::NextNodeName(const std::string& config_name,
                                     const std::string& entrypoint_name) {
  int index = next_index_[config_name]++;
  return absl::StrCat(config_name, "-", index, "-", entrypoint_name);
}

NodeId OakRuntime::NextNodeId() { return next_node_id_++; }

// Create (but don't start) a new Node instance.  Return a borrowed pointer to
// the new Node (or nullptr on failure).
OakNode* OakRuntime::CreateNode(const std::string& config_name, const std::string& entrypoint_name,
                                NodeId node_id, std::string* node_name) {
  std::string name = NextNodeName(config_name, entrypoint_name);
  std::unique_ptr<OakNode> node;

  if (wasm_config_.count(config_name) > 0) {
    OAK_LOG(INFO) << "Create Wasm node named {" << name << "}";
    const WebAssemblyConfiguration* wasm_cfg = wasm_config_[config_name].get();
    node = WasmNode::Create(this, name, node_id, wasm_cfg->module_bytes(), entrypoint_name);
  } else if (log_config_.count(config_name) > 0) {
    OAK_LOG(INFO) << "Create log node named {" << name << "}";
    node = absl::make_unique<LoggingNode>(this, name, node_id);
  } else if (storage_config_.count(config_name) > 0) {
    std::string address = *(storage_config_[config_name].get());
    OAK_LOG(INFO) << "Create storage proxy node named {" << name << "} connecting to " << address;
    node = absl::make_unique<StorageNode>(this, name, node_id, address);
  } else if (grpc_client_config_.count(config_name) > 0) {
    std::string address = *(grpc_client_config_[config_name].get());
    OAK_LOG(INFO) << "Create gRPC client node named {" << name << "} connecting to " << address;
    node = absl::make_unique<GrpcClientNode>(this, name, node_id, address);
  } else {
    OAK_LOG(ERROR) << "failed to find config with name " << config_name;
    return nullptr;
  }

  OakNode* result = node.get();
  if (node != nullptr) {
    nodes_[name] = std::move(node);
    *node_name = name;
  } else {
    OAK_LOG(ERROR) << "failed to create Node with config of name " << config_name;
  }
  return result;
}

bool OakRuntime::CreateAndRunNode(const std::string& config_name,
                                  const std::string& entrypoint_name,
                                  std::unique_ptr<ChannelHalf> half, std::string* node_name) {
  if (TerminationPending()) {
    OAK_LOG(WARNING) << "Runtime is pending termination, fail node creation";
    return false;
  }

  absl::MutexLock lock(&mu_);
  NodeId node_id = NextNodeId();
  OakNode* node = CreateNode(config_name, entrypoint_name, node_id, node_name);
  if (node == nullptr) {
    return false;
  }

  // Add the given channel as the Node's single available handle.
  Handle handle = node->AddChannel(std::move(half));

  OAK_LOG(INFO) << "Start node named {" << *node_name << "} with initial handle " << handle;
  node->Start(handle);
  return true;
}

grpc::Status OakRuntime::Start() {
  OAK_LOG(INFO) << "Starting runtime";

  // Now all dependencies are running, start the initial pair of Nodes running.
  grpc_node_->Start(grpc_handle_);
  app_node_->Start(app_handle_);

  return grpc::Status::OK;
}

int32_t OakRuntime::GetPort() { return grpc_node_->GetPort(); }

grpc::Status OakRuntime::Stop() {
  OAK_LOG(INFO) << "Stopping runtime...";
  termination_pending_ = true;

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
    OAK_LOG(INFO) << "Stopping node " << named_node.first;
    named_node.second->Stop();
  }

  return grpc::Status::OK;
}

}  // namespace oak

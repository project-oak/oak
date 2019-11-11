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

#include "oak/common/app_config.h"

#include <set>
#include <utility>

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"

namespace oak {

// Names of ports that are implicitly defined for pseudo-Node instances,
// as described in //oak/proto/manager.proto.
const char kGrpcNodeRequestPortName[] = "request";
const char kLoggingNodePortName[] = "in";
const char kStorageNodeRequestPortName[] = "request";
const char kStorageNodeResponsePortName[] = "response";
const char kEscrowNodeRequestPortName[] = "request";
const char kEscrowNodeResponsePortName[] = "response";

namespace {

// Conventional names for pseudo-node instances (not specified in the proto
// definition).
constexpr char kGrpcNodeName[] = "grpc";
constexpr char kLogNodeName[] = "log";
constexpr char kStorageNodeName[] = "storage";
constexpr char kEscrowNodeName[] = "escrow";

// Conventional names for the ports that connect to pseudo-node instances (not
// specified in the proto definition).
constexpr char kGrpcInPortName[] = "grpc_in";
constexpr char kStorageInPortName[] = "storage_in";
constexpr char kStorageOutPortName[] = "storage_out";

}  // namespace

std::unique_ptr<ApplicationConfiguration> DefaultConfig(const std::string& name,
                                                        const std::string& module_bytes) {
  auto config = absl::make_unique<ApplicationConfiguration>();

  Node* grpc_node = config->add_nodes();
  grpc_node->set_node_name(kGrpcNodeName);
  grpc_node->mutable_grpc_server_node();

  Node* node = config->add_nodes();
  node->set_node_name(name);

  WebAssemblyNode* wasm_node = node->mutable_web_assembly_node();
  std::string contents_name = name + "-code";
  wasm_node->set_wasm_contents_name(contents_name);

  WasmContents* wasm_contents = config->add_wasm_contents();
  wasm_contents->set_name(contents_name);
  wasm_contents->set_module_bytes(module_bytes);

  // Add port for this Wasm node to receive from the gRPC pseudo-Node.
  Port* in_port = wasm_node->add_ports();
  in_port->set_name(kGrpcInPortName);
  in_port->set_type(Port_Type_IN);

  // Join up channels.
  Channel* in_channel = config->add_channels();
  Channel_Endpoint* in_src = in_channel->mutable_source_endpoint();
  in_src->set_node_name(grpc_node->node_name());
  in_src->set_port_name(kGrpcNodeRequestPortName);
  Channel_Endpoint* in_dest = in_channel->mutable_destination_endpoint();
  in_dest->set_node_name(node->node_name());
  in_dest->set_port_name(in_port->name());

  return config;
}

void AddLoggingToConfig(ApplicationConfiguration* config) {
  // Add the logging pseudo-Node.
  Node* log_node = config->add_nodes();
  log_node->set_node_name(kLogNodeName);  // Assume name not already used.
  log_node->mutable_log_node();

  // Connect all Wasm nodes to it.
  for (auto& node : *config->mutable_nodes()) {
    if (!node.has_web_assembly_node()) {
      continue;
    }
    // Add a port for this Wasm node to talk to the logging pseudo-Node.
    WebAssemblyNode* wasm_node = node.mutable_web_assembly_node();
    Port* log_port = wasm_node->add_ports();
    log_port->set_name(kLogNodeName);  // Assume name not already used.
    log_port->set_type(Port_Type_OUT);

    // Add a channel connecting this port to the logging pseudo-Node.
    Channel* channel = config->add_channels();
    Channel_Endpoint* src = channel->mutable_source_endpoint();
    src->set_node_name(node.node_name());
    src->set_port_name(log_port->name());
    Channel_Endpoint* dest = channel->mutable_destination_endpoint();
    dest->set_node_name(log_node->node_name());
    dest->set_port_name(kLoggingNodePortName);
  }
}

bool AddStorageToConfig(ApplicationConfiguration* config, const std::string& name,
                        const std::string& storage_address) {
  for (auto& node : *config->mutable_nodes()) {
    if (!node.has_web_assembly_node() || node.node_name() != name) {
      continue;
    }
    // Add the storage pseudo-Node.
    Node* storage_node = config->add_nodes();
    storage_node->set_node_name(kStorageNodeName);  // Assume name not already used.
    storage_node->mutable_storage_node()->set_address(storage_address);

    // Add ports for this Wasm node to talk to storage.
    WebAssemblyNode* wasm_node = node.mutable_web_assembly_node();
    Port* out_port = wasm_node->add_ports();
    out_port->set_name(kStorageOutPortName);  // Assume name not already used.
    out_port->set_type(Port_Type_OUT);
    Port* in_port = wasm_node->add_ports();
    in_port->set_name(kStorageInPortName);  // Assume name not already used.
    in_port->set_type(Port_Type_IN);

    // Add channels connecting these ports to the storage pseudo-Node.
    Channel* out_channel = config->add_channels();
    Channel_Endpoint* out_src = out_channel->mutable_source_endpoint();
    out_src->set_node_name(node.node_name());
    out_src->set_port_name(out_port->name());
    Channel_Endpoint* out_dest = out_channel->mutable_destination_endpoint();
    out_dest->set_node_name(storage_node->node_name());
    out_dest->set_port_name(kStorageNodeRequestPortName);

    Channel* in_channel = config->add_channels();
    Channel_Endpoint* in_src = in_channel->mutable_source_endpoint();
    in_src->set_node_name(storage_node->node_name());
    in_src->set_port_name(kStorageNodeResponsePortName);
    Channel_Endpoint* in_dest = in_channel->mutable_destination_endpoint();
    in_dest->set_node_name(node.node_name());
    in_dest->set_port_name(in_port->name());
    return true;
  }
  LOG(ERROR) << "Failed to find Wasm node " << name;
  return false;
}

bool AddEscrowToConfig(ApplicationConfiguration* config, const std::string& name,
                        const std::string& storage_address) {
  for (auto& node : *config->mutable_nodes()) {
    if (!node.has_storage_node() || node.node_name() != name) {
      continue;
    }
    Node* escrow_node = config->add_nodes();
    escrow_node->set_node_name(kEscrowNodeName);
    escrow_node->mutable_escrow_node()->set_address(storage_address);

    StorageProxyNode* storage_node = node.mutable_storage_node();
    Port* out_port = storage_node->add_ports();
    out_port->set_name(kEscrowOutPortName);
    out_port->set_type(Port_Type_OUT);
    Port* in_port = storage_node->add_ports();
    in_port->set_name(kEscrowInPortName);
    in_port->set_type(Port_Type_IN);

    Channel* out_channel = config->add_channels();
    Channel_Endpoint* out_src = out_channel->mutable_source_endpoint();
    out_src->set_node_name(node.node_name());
    out_src->set_port_name(out_port->name());
    Channel_Endpoint* out_dest = out_channel->mutable_destination_endpoint();
    out_dest->set_node_name(escrow_node->node_name());
    out_dest->set_port_name(kEscrowNodeRequestPortName);

    Channel* in_channel = config->add_channels();
    Channel_Endpoint* in_src = in_channel->mutable_source_endpoint();
    in_src->set_node_name(escrow_node->node_name());
    in_src->set_port_name(kEscrowNodeResponsePortName);
    Channel_Endpoint* in_dest = in_channel->mutable_destination_endpoint();
    in_dest->set_node_name(node.node_name());
    in_dest->set_port_name(in_port->name());
    return true;
  }
  LOG(ERROR) << "Failed to find Storage node " << name;
  return false;
}

bool ValidApplicationConfig(const ApplicationConfiguration& config) {
  // Check name uniqueness for WasmContents.
  std::set<std::string> contents_names;
  for (const auto& contents : config.wasm_contents()) {
    if (contents_names.count(contents.name()) > 0) {
      LOG(ERROR) << "duplicate Wasm contents name " << contents.name();
      return false;
    }
    contents_names.insert(contents.name());
  }

  // Check name uniqueness and count pseudo-nodes.  Along the way, track the
  // configured directions of each "fully-qualified port name" (fqpn).
  using fqpn = std::pair<std::string, std::string>;  // <node name, port name>
  std::map<fqpn, int> in_ports;                      // fqpn -> number of channels
  std::map<fqpn, int> out_ports;
  std::set<std::string> node_names;
  int wasm_count = 0;
  int grpc_count = 0;
  int log_count = 0;
  for (const auto& node : config.nodes()) {
    if (node_names.count(node.node_name()) > 0) {
      LOG(ERROR) << "duplicate node name " << node.node_name();
      return false;
    }
    node_names.insert(node.node_name());

    if (node.has_web_assembly_node()) {
      wasm_count++;
      const auto& wasm_node = node.web_assembly_node();

      // Check that the Wasm code is available.
      if (contents_names.count(wasm_node.wasm_contents_name()) == 0) {
        LOG(ERROR) << "node " << node.node_name() << " refers to undefined Wasm code "
                   << wasm_node.wasm_contents_name();
        return false;
      }

      // Check that port names are unique across the Node.
      std::set<std::string> port_names;
      for (const auto& port : wasm_node.ports()) {
        if (port_names.count(port.name()) > 0) {
          LOG(ERROR) << "duplicate port name " << port.name() << " for node " << node.node_name();
          return false;
        }
        port_names.insert(port.name());

        // Track which node.port instances are IN/OUT.
        if (port.type() == Port_Type_IN) {
          in_ports[fqpn(node.node_name(), port.name())] = 0;
        } else if (port.type() == Port_Type_OUT) {
          out_ports[fqpn(node.node_name(), port.name())] = 0;
        }
      }
    } else if (node.has_grpc_server_node()) {
      grpc_count++;
      out_ports[fqpn(node.node_name(), kGrpcNodeRequestPortName)] = 0;
    } else if (node.has_log_node()) {
      in_ports[fqpn(node.node_name(), kLoggingNodePortName)] = 0;
      log_count++;
    } else if (node.has_storage_node()) {
      in_ports[fqpn(node.node_name(), kStorageNodeRequestPortName)] = 0;
      out_ports[fqpn(node.node_name(), kStorageNodeResponsePortName)] = 0;
      in_ports[fqpn(node.node_name(), kEscrowInPortName)] = 0;
      out_ports[fqpn(node.node_name(), kEscrowOutPortName)] = 0;
    } else if (node.has_escrow_node()) {
      in_ports[fqpn(node.node_name(), kEscrowNodeRequestPortName)] = 0;
      out_ports[fqpn(node.node_name(), kEscrowNodeResponsePortName)] = 0;
    }
  }

  // Check constraints on numbers of node types.
  if (wasm_count == 0) {
    LOG(ERROR) << "no WebAssembly node included";
    return false;
  }
  if (grpc_count > 1) {
    LOG(ERROR) << "multiple gRPC pseudo-nodes included";
    return false;
  }
  if (log_count > 1) {
    LOG(ERROR) << "multiple logging pseudo-nodes included";
    return false;
  }

  // Check all channels connect up properly.
  for (const auto& channel : config.channels()) {
    fqpn source(channel.source_endpoint().node_name(), channel.source_endpoint().port_name());
    fqpn dest(channel.destination_endpoint().node_name(),
              channel.destination_endpoint().port_name());

    if (out_ports.count(source) == 0) {
      LOG(ERROR) << "channel refers to unknown source endpoint " << source.first << "."
                 << source.second;
      return false;
    }
    if (in_ports.count(dest) == 0) {
      LOG(ERROR) << "channel refers to unknown destination endpoint " << dest.first << "."
                 << dest.second;
      return false;
    }
    out_ports[source]++;
    in_ports[dest]++;
  }
  // Check output ports have exactly one connected channel.
  for (const auto& it : out_ports) {
    if (it.second != 1) {
      LOG(ERROR) << "output port " << it.first.first << "." << it.first.second << " has "
                 << it.second << " channels from it";
      return false;
    }
  }
  // Check input ports have at least one connected channel.
  for (const auto& it : in_ports) {
    if (it.second == 0) {
      LOG(ERROR) << "input port " << it.first.first << "." << it.first.second
                 << " has no channels to it";
      return false;
    }
  }

  return true;
}

}  // namespace oak

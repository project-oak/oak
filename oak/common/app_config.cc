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

#include "asylo/util/logging.h"

namespace oak {

bool ValidApplicationConfig(const ApplicationConfiguration& config) {
  // Check name uniqueness and count pseudo-nodes.  Along the way, track the
  // configured directions of each "fully-qualified port name" (fqpn).
  using fqpn = std::pair<std::string, std::string>;  // <node name, port name>
  std::set<fqpn> in_ports;
  std::set<fqpn> out_ports;
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
      // Check that port names are unique across the Node.
      const auto& wasm_node = node.web_assembly_node();
      std::set<std::string> port_names;
      for (const auto& port : wasm_node.ports()) {
        if (port_names.count(port.name()) > 0) {
          LOG(ERROR) << "duplicate port name " << port.name() << " for node " << node.node_name();
          return false;
        }
        port_names.insert(port.name());

        // Track which node.port instances are IN/OUT.
        if (port.type() == Port_Type_IN) {
          in_ports.insert(fqpn(node.node_name(), port.name()));
        } else if (port.type() == Port_Type_OUT) {
          out_ports.insert(fqpn(node.node_name(), port.name()));
        }
      }
    } else if (node.has_grpc_server_node()) {
      grpc_count++;
      in_ports.insert(fqpn(node.node_name(), "response"));
      out_ports.insert(fqpn(node.node_name(), "request"));
    } else if (node.has_log_node()) {
      in_ports.insert(fqpn(node.node_name(), "in"));
      log_count++;
    } else if (node.has_storage_node()) {
      in_ports.insert(fqpn(node.node_name(), "request"));
      out_ports.insert(fqpn(node.node_name(), "response"));
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
  }

  return true;
}

}  // namespace oak

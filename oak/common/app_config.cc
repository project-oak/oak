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
#include "oak/common/utils.h"

#include <set>
#include <utility>

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"

namespace oak {

namespace {

// Conventional names for the configuration of Nodes.
constexpr char kAppConfigName[] = "app";
constexpr char kAppEntrypointName[] = "oak_main";
constexpr char kLogConfigName[] = "log";
constexpr char kStorageConfigName[] = "storage";

}  // namespace

std::unique_ptr<ApplicationConfiguration> DefaultConfig(const std::string& module_bytes) {
  auto config = absl::make_unique<ApplicationConfiguration>();

  config->set_initial_node(kAppConfigName);
  NodeConfiguration* node_config = config->add_node_configs();
  node_config->set_name(kAppConfigName);
  WebAssemblyConfiguration* code = node_config->mutable_wasm_config();
  code->set_module_bytes(module_bytes);
  code->set_main_entrypoint(kAppEntrypointName);

  return config;
}

std::unique_ptr<ApplicationConfiguration> ReadConfigFromFile(const std::string& filename) {
  auto config = absl::make_unique<ApplicationConfiguration>();

  std::string data = utils::read_file(filename);
  config->ParseFromString(data);

  return config;
}

void WriteConfigToFile(const ApplicationConfiguration* config, const std::string& filename) {
  std::string data = config->SerializeAsString();
  utils::write_file(data, filename);
}

void AddLoggingToConfig(ApplicationConfiguration* config) {
  NodeConfiguration* node_config = config->add_node_configs();
  node_config->set_name(kLogConfigName);
  node_config->mutable_log_config();
}

void AddStorageToConfig(ApplicationConfiguration* config, const std::string& storage_address) {
  NodeConfiguration* node_config = config->add_node_configs();
  node_config->set_name(kStorageConfigName);
  StorageProxyConfiguration* storage = node_config->mutable_storage_config();
  storage->set_address(storage_address);
}

void AddGrpcPortToConfig(ApplicationConfiguration* config, const int16_t grpc_port) {
  config->set_grpc_port(grpc_port);
}

bool ValidApplicationConfig(const ApplicationConfiguration& config) {
  // Check name uniqueness for NodeConfiguration.
  std::set<std::string> config_names;
  std::set<std::string> wasm_names;
  for (const auto& node_config : config.node_configs()) {
    if (config_names.count(node_config.name()) > 0) {
      LOG(ERROR) << "duplicate node config name " << node_config.name();
      return false;
    }
    config_names.insert(node_config.name());
    if (node_config.has_wasm_config()) {
      wasm_names.insert(node_config.name());
      if (node_config.wasm_config().main_entrypoint().empty()) {
        LOG(ERROR) << "missing entrypoint for Wasm node of name " << node_config.name();
        return false;
      }
    }
  }

  // Check name for the config of the initial node is present and is a Web
  // Assembly variant.
  if (wasm_names.count(config.initial_node()) == 0) {
    return false;
  }
  return true;
}

}  // namespace oak

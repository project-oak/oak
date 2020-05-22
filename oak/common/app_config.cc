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
#include "glog/logging.h"
#include "oak/common/utils.h"

using ::oak::application::ApplicationConfiguration;
using ::oak::application::NodeConfiguration;

namespace oak {

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
    }
  }

  // Check name for the config of the initial node is present and is a Web
  // Assembly variant.
  if (wasm_names.count(config.initial_node_config_name()) == 0) {
    LOG(ERROR) << "config of the initial node is not present in Wasm";
    return false;
  }
  if (config.initial_entrypoint_name().empty()) {
    LOG(ERROR) << "missing entrypoint name";
    return false;
  }
  return true;
}

}  // namespace oak

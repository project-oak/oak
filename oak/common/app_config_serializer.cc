/*
 * Copyright 2020 The Project Oak Authors
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

#include <memory>
#include <string>
#include <map>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/memory/memory.h"
#include "absl/strings/str_split.h"
#include "asylo/util/logging.h"
#include "google/protobuf/text_format.h"
#include "oak/common/app_config.h"
#include "oak/common/utils.h"

ABSL_FLAG(std::string, textproto, "", "Textproto file with application configuration");
ABSL_FLAG(std::vector<std::string>, modules, std::vector<std::string>{},
          "A comma-separated list of entries `module=path` "
          "with files containing compiled WebAssembly modules");
ABSL_FLAG(std::string, output_file, "", "File to write an application configuration to");

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);
  std::string textproto = absl::GetFlag(FLAGS_textproto);
  if (textproto.empty()) {
    LOG(QFATAL) << "Textproto file is not specified";
    return 1;
  }
  std::vector<std::string> modules = absl::GetFlag(FLAGS_modules);
  if (modules.empty()) {
    LOG(QFATAL) << "Wasm modules are not specified";
    return 1;
  }
  std::string output_file = absl::GetFlag(FLAGS_output_file);
  if (output_file.empty()) {
    LOG(QFATAL) << "Output file is not specified";
    return 1;
  }

  // Parse module names.
  std::map<std::string, std::string> module_map;
  for (const std::string& module : absl::GetFlag(FLAGS_modules)) {
    std::vector<std::string> module_info = absl::StrSplit(module, '=');
    if (module_info.size() != 2) {
      LOG(QFATAL) << "Incorrect module specification:" << module;
      return 1;
    }
    module_map.emplace(module_info.front(), module_info.back());
  }

  // Load application configuration.
  auto config = absl::make_unique<oak::ApplicationConfiguration>();
  google::protobuf::TextFormat::MergeFromString(textproto, config.get());

  // Add Wasm module bytes to the application configuration.
  for (auto& node_config : *config->mutable_node_configs()) {
    auto it = module_map.find(node_config.name());
    if (it != module_map.end()) {
      std::string module_bytes = oak::utils::read_file(it->second);
      node_config.mutable_wasm_config()->set_module_bytes(module_bytes);
    } else {
      LOG(QFATAL) << "Module path for " << it->first << " is not specified";
      return 1;
    }
  }

  oak::WriteConfigToFile(config.get(), output_file);
  return 0;
}

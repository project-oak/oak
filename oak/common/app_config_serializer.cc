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

#include <map>
#include <memory>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/memory/memory.h"
#include "absl/strings/str_split.h"
#include "asylo/util/logging.h"
#include "google/protobuf/text_format.h"
#include "oak/common/app_config.h"
#include "oak/common/utils.h"

ABSL_FLAG(
    std::string, textproto, "",
    "Textproto file with an application configuration, where the `module_bytes` value is empty, "
    "(it will be overwritten by module bytes after serialization)");
ABSL_FLAG(std::vector<std::string>, modules, std::vector<std::string>{},
          "A comma-separated list of entries `module:path` with files containing compiled "
          "WebAssembly modules to insert into the generated configuration");
ABSL_FLAG(std::string, output_file, "", "File to write an application configuration to");

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);
  std::string textproto = absl::GetFlag(FLAGS_textproto);
  if (textproto.empty()) {
    LOG(QFATAL) << "Textproto file is not specified";
  }
  std::vector<std::string> modules = absl::GetFlag(FLAGS_modules);
  if (modules.empty()) {
    LOG(QFATAL) << "Wasm modules are not specified";
  }
  std::string output_file = absl::GetFlag(FLAGS_output_file);
  if (output_file.empty()) {
    LOG(QFATAL) << "Output file is not specified";
  }

  // Parse module names.
  std::map<std::string, std::string> module_map;
  for (const std::string& module : absl::GetFlag(FLAGS_modules)) {
    std::vector<std::string> module_info = absl::StrSplit(module, ':');
    if (module_info.size() != 2) {
      LOG(QFATAL) << "Incorrect module specification: " << module;
    }
    module_map.emplace(module_info.front(), module_info.back());
  }

  // Load application configuration.
  auto config = absl::make_unique<oak::ApplicationConfiguration>();
  std::string textproto_string = oak::utils::read_file(textproto);
  google::protobuf::TextFormat::MergeFromString(textproto_string, config.get());

  // Add Wasm module bytes to the application configuration.
  for (auto& node_config : *config->mutable_node_configs()) {
    if (node_config.has_wasm_config()) {
      std::string module_name = node_config.name();
      auto it = module_map.find(module_name);
      if (it != module_map.end()) {
        std::string module_bytes = oak::utils::read_file(it->second);
        if (module_bytes.empty()) {
          LOG(QFATAL) << "Empty Wasm module:" << module_name;
        }
        node_config.mutable_wasm_config()->set_module_bytes(module_bytes);
      } else {
        LOG(QFATAL) << "Module path for " << module_name << " is not specified";
      }
    }
  }

  // Check application configuration validity.
  if (!oak::ValidApplicationConfig(*config.get())) {
    LOG(QFATAL) << "Application config is not valid";
  }

  oak::WriteConfigToFile(config.get(), output_file);
  return 0;
}

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
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "oak/common/app_config.h"
#include "oak/common/utils.h"

ABSL_FLAG(
    std::string, textproto, "",
    "Textproto file with an application configuration, where the `wasm_modules` field is empty, "
    "(it will be overwritten by module bytes after serialization)");
ABSL_FLAG(std::vector<std::string>, modules, std::vector<std::string>{},
          "A comma-separated list of entries `module_name:path` with files containing compiled "
          "WebAssembly modules to insert into the generated configuration");
ABSL_FLAG(std::string, output_file, "", "File to write an application configuration to");

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);
  std::string textproto = absl::GetFlag(FLAGS_textproto);
  if (textproto.empty()) {
    LOG(FATAL) << "Textproto file is not specified";
    return 1;
  }
  std::vector<std::string> modules = absl::GetFlag(FLAGS_modules);
  if (modules.empty()) {
    LOG(FATAL) << "Wasm modules are not specified";
    return 1;
  }
  std::string output_file = absl::GetFlag(FLAGS_output_file);
  if (output_file.empty()) {
    LOG(FATAL) << "Output file is not specified";
    return 1;
  }

  // Load application configuration.
  auto config = absl::make_unique<oak::application::ApplicationConfiguration>();
  std::string textproto_string = oak::utils::read_file(textproto);
  if (!google::protobuf::TextFormat::MergeFromString(textproto_string, config.get())) {
    LOG(FATAL) << "Error parsing proto";
    return 1;
  }

  // Parse module names and add Wasm module bytes to the application configuration.
  std::map<std::string, std::string> module_map;
  for (const std::string& module : absl::GetFlag(FLAGS_modules)) {
    std::vector<std::string> module_info = absl::StrSplit(module, ':');
    if (module_info.size() != 2) {
      LOG(FATAL) << "Incorrect module specification: " << module;
      return 1;
    }
    std::string module_name = module_info[0];
    std::string module_path = module_info[1];
    std::string module_bytes = oak::utils::read_file(module_path);
    if (module_bytes.empty()) {
      LOG(FATAL) << "Empty Wasm module:" << module_name;
      return 1;
    }
    (*config->mutable_wasm_modules())[module_name] = std::move(module_bytes);
  }

  // Check application configuration validity.
  if (!oak::ValidApplicationConfig(*config)) {
    LOG(FATAL) << "Application config is not valid";
    return 1;
  }

  oak::WriteConfigToFile(config.get(), output_file);
  return 0;
}

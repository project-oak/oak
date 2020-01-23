//
// Copyright 2019 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_
#define OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_

// Application config as text proto. Deliberately use non-default names for
// node configs to confirm that nothing has been accidentally hard-coded.
static const char* app_config_textproto = R"raw(
node_configs {
  name: "frontend-config"
  wasm_config {
    module_bytes: "<filled in later>"
  }
}
node_configs {
  name: "backend-config"
  wasm_config {
    module_bytes: "<filled in later>"
  }
}
node_configs {
  name: "logging-config"
  log_config {}
}
initial_node_config_name: "frontend-config"
initial_entrypoint_name: "frontend_oak_main"
)raw";

#endif  // OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_

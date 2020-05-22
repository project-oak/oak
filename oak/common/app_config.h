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

#ifndef OAK_COMMON_APP_CONFIG_H_
#define OAK_COMMON_APP_CONFIG_H_

#include <memory>

#include "oak/proto/application.pb.h"

namespace oak {

// Reads a serialized application configuration from file.
std::unique_ptr<application::ApplicationConfiguration> ReadConfigFromFile(
    const std::string& filename);

// Serializes an application configuration from `config` and writes it into a file.
void WriteConfigToFile(const application::ApplicationConfiguration* config,
                       const std::string& filename);

// Checks whether the given ApplicationConfiguration is valid.
bool ValidApplicationConfig(const application::ApplicationConfiguration& config);

}  // namespace oak

#endif  // OAK_COMMON_APP_CONFIG_H_

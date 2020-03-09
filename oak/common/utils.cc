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

#include "oak/common/utils.h"

#include <fstream>
#include <sstream>

#include "oak/common/logging.h"

namespace oak {
namespace utils {

std::string read_file(const std::string& filename) {
  std::ifstream t(filename, std::ifstream::in);
  if (!t.is_open()) {
    OAK_LOG(FATAL) << "Could not open file '" << filename << "'";
  }
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

void write_file(const std::string& data, const std::string& filename) {
  std::ofstream t(filename, std::ofstream::out);
  if (!t.is_open()) {
    OAK_LOG(FATAL) << "Could not open file '" << filename << "'";
  }
  t << data;
  t.close();
}

}  // namespace utils
}  // namespace oak

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
#include <map>
#include <regex>

#include "glog/logging.h"

namespace oak {
namespace utils {

std::string read_file(const std::string& filename) {
  std::ifstream t(filename, std::ifstream::in);
  if (!t.is_open()) {
    LOG(FATAL) << "Could not open file '" << filename << "'";
  }
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

void write_file(const std::string& data, const std::string& filename) {
  std::ofstream t(filename, std::ofstream::out);
  if (!t.is_open()) {
    LOG(FATAL) << "Could not open file '" << filename << "'";
  }
  t << data;
  t.close();
}

std::map<std::string, std::string> read_pem(const std::string& filename) {
  std::map<std::string, std::string> content;
  std::ifstream pem_file(filename, std::ifstream::in);
  if (!pem_file.is_open()) {
    LOG(FATAL) << "Could not open file '" << filename << "'";
  }

  std::string line;
  std::regex header_regex("-----BEGIN (.*)-----");
  while (std::getline(pem_file, line)) {
    std::smatch header_match;
    if (std::regex_search(line, header_match, header_regex)) {
      std::string header = header_match[1].str();
      std::string footer = "-----END " + header + "-----";
      std::string value;
      while (std::getline(pem_file, line) && line.find(footer) == std::string::npos) {
        value.append(line);
      }
      content[header] = value;
    }
  }
  return content;
}

void write_pem(const std::map<std::string, std::string>& map, const std::string& filename) {
  std::ofstream out_file(filename, std::ofstream::out);
  if (!out_file.is_open()) {
    LOG(FATAL) << "Could not open file '" << filename << "'";
  }
  for (const auto& item : map) {
    std::string header = "-----BEGIN " + item.first + "-----";
    std::string footer = "-----END " + item.first + "-----";

    out_file << header << "\n";
    out_file << item.second << "\n";
    out_file << footer << "\n";
  }
  out_file.close();
}

}  // namespace utils
}  // namespace oak

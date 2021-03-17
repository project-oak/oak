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

#include "absl/strings/escaping.h"
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
  auto pem_encoded_data = read_file(filename);
  return decode_pem(pem_encoded_data);
}

std::map<std::string, std::string> decode_pem(const std::string& pem_encoded_data) {
  std::map<std::string, std::string> content;
  std::stringstream streamed_pem(pem_encoded_data);
  std::string line;

  std::regex header_regex("-----BEGIN (.*)-----");
  while (std::getline(streamed_pem, line, '\n')) {
    std::smatch header_match;
    if (std::regex_search(line, header_match, header_regex)) {
      std::string header = header_match[1].str();
      std::string footer = "-----END " + header + "-----";
      std::string value;
      // Build the value by concatenating all the lines between the header and the footer.
      while (std::getline(streamed_pem, line, '\n') && line.find(footer) == std::string::npos) {
        value.append(line);
      }
      std::string decoded_value;
      if (!absl::Base64Unescape(value, &decoded_value)) {
        LOG(FATAL) << "Could not decode base64 value.";
      };
      content[header] = decoded_value;
    }
  }
  return content;
}

void write_pem(const std::map<std::string, std::string>& map, const std::string& filename) {
  std::ofstream out_file(filename, std::ofstream::out);
  if (!out_file.is_open()) {
    LOG(FATAL) << "Could not open file '" << filename << "'";
  }

  auto pem_encoded_data = encode_pem(map);
  out_file << pem_encoded_data;

  out_file.close();
}

std::string encode_pem(const std::map<std::string, std::string>& map) {
  std::stringstream buffer;
  for (const auto& item : map) {
    std::string header = "-----BEGIN " + item.first + "-----";
    std::string footer = "-----END " + item.first + "-----";

    buffer << header << "\n";
    buffer << absl::Base64Escape(item.second) << "\n";
    buffer << footer << "\n\n";
  }
  return buffer.str();
}

}  // namespace utils
}  // namespace oak

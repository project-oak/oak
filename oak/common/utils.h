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

#ifndef OAK_COMMON_UTILS_H_
#define OAK_COMMON_UTILS_H_

#include <map>
#include <string>

namespace oak {
namespace utils {

// Reads a binary file and returns its contents as a std::string.
std::string read_file(const std::string& filename);

// Writes `data` string into a binary file.
void write_file(const std::string& data, const std::string& filename);

// Read a PEM file into a keys and values map.
std::map<std::string, std::string> read_pem(const std::string& filename);

// Write the given key-value pairs as a PEM file.
void write_pem(const std::map<std::string, std::string>& map, const std::string& filename);

// Encode the given key-value pairs as a PEM.
std::string encode_pem(const std::map<std::string, std::string>& map);

// Decode the given PEM-encoded string into a keys and values map.
std::map<std::string, std::string> decode_pem(const std::string& pem_encoded_data);

}  // namespace utils
}  // namespace oak

#endif  // OAK_COMMON_UTILS_H_

/*
 * Copyright 2021 The Project Oak Authors
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

#include <string>

namespace oak {

// Generates an X25519 key pair, and writes them as Base64-encoded strings in two separate files in
// the provided paths.
void generate(const std::string& private_key_path, const std::string& public_key_path);

// Signs the sha256 hash of the message using the given private key. Returns the base64 hash of the
// signature.
std::string sign(const std::string& private_key_path, const std::string& input_string);

}  // namespace oak

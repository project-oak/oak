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

#include "oak_abi/proto/identity.pb.h"

namespace oak {

// Generates an Ed25519 key pair, and return the private key. The public key can be generated from
// the private key.
std::string generate();

// Store the given private key as a base64 encoded string in a PEM file in the given path.
void store_private_key(const std::string& private_key, const std::string& private_key_path);

// Signs the sha256 hash of the message using the given private key. Returns a SignedChallenge
// containing the signed hash and the public key corresponding to the input private key.
oak::identity::SignedChallenge sign(const std::string& private_key,
                                    const std::string& input_string);

}  // namespace oak

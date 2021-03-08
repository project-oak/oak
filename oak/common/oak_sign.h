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

#include "absl/base/attributes.h"
#include "oak_abi/proto/identity.pb.h"

namespace oak {

// `PRIVATE KEY` tag for reading and writing from and to PEM files.
ABSL_CONST_INIT extern const char kPrivateKeyPemTag[];

// Generates an ed25519 key pair, and return the private key. The public key can be derived from
// the private key.
std::string generate_ed25519_key_pair();

// Stores the given private key as a base64 encoded string in a PEM file in the given path.
void store_private_key(const std::string& private_key, const std::string& private_key_path);

// Signs the sha256 hash of the message using the given private key. Returns a SignedChallenge
// containing the signed hash and the public key corresponding to the input private key.
oak::identity::SignedChallenge sign_ed25519(const std::string& private_key,
                                            const std::string& input_string);

// Computes the sha256 hash of the unhashed input string. Returns true if hashing is successful. In
// this case the hashed value is stored in the second input parameter.
bool compute_sha256_hash(const std::string& unhashed, std::string& hashed);

}  // namespace oak

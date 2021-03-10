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
#include "tink/signature/ed25519_sign_key_manager.h"

using ::google::crypto::tink::Ed25519PrivateKey;

namespace oak {

// `PRIVATE KEY` tag for reading and writing from and to PEM files.
ABSL_CONST_INIT extern const char kPrivateKeyPemTag[];

struct Signature {
  std::string signed_hash;
  std::string public_key;
};

class KeyPair {
 public:
  KeyPair(const std::string& private_key);

  // Signs the sha256 hash of the given message using private key in this KeyPair. Returns a
  // Signature containing the signed hash and the public key in this KeyPair.
  Signature Sign(const std::string& message);

  std::string GetPublicKey() { return key_.public_key().key_value(); }
  std::string GetPrivateKey() { return key_.key_value(); }

  // Generates a new KeyPair instance containing an ed25519 key pair.
  static std::unique_ptr<KeyPair> Generate();

 private:
  Ed25519PrivateKey key_;
  KeyPair(const Ed25519PrivateKey private_key) : key_(private_key) {}
};

// Computes the sha256 hash of the unhashed input string. Returns true if hashing is successful. In
// this case the hashed value is stored in the second input parameter.
bool compute_sha256_hash(const std::string& unhashed, std::string& hashed);

}  // namespace oak

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
  std::string public_key_der;
};

class KeyPair {
 public:
  // Signs the sha256 hash of the given message using private key in this KeyPair. Returns a
  // Signature containing the signed hash and the public key in this KeyPair.
  Signature Sign(const std::string& message);

  // Generates a PKCS#8 encoded string from this key pair.
  std::string ToPkcs8();

  // Returns the public key, as a raw Ed25519 key.
  std::string GetPublicKeyRaw() { return key_.public_key().key_value(); }

  // Returns the public key, as a binary DER-encoded SubjectPublicKeyInfo (see
  // https://tools.ietf.org/html/rfc5280#section-4.1).
  std::string GetPublicKeyDer() {
    // Since Tink does not have functions to convert to / from ASN.1, we fake this by manually
    // pre-computing and hardcoding a fixed prefix that, when concatenated with the actual raw key
    // bytes, produces a valid ASN.1-encoded Ed25519 public key.
    //
    // This is the meaning of the prefix bytes interpreted as ASN.1:
    //
    // 30 2a                : SEQUENCE len 42 (SubjectPublicKeyInfo)
    //     30 05            : SEQUENCE len 5 (AlgorithmIdentifier)
    //        06 03         : OBJECT IDENTIFIER len 3
    //           2b6570     : 1.3.101.112 = Ed25519
    //     03 21            : BIT STRING len 33
    //        00            : number of padding bits at end of content
    //        7f8d520a536d4788b8eafd93ba1d5f40b6edfd9a91af594435a8c25bdda3c8fe : [raw public key]
    //
    // Also see:
    //
    // - https://github.com/project-oak/oak/issues/1912#issuecomment-802689201
    // - https://tools.ietf.org/html/rfc5280#section-4.1 (SubjectPublicKeyInfo)
    return std::string({0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00}) +
           key_.public_key().key_value();
  }
  std::string GetPrivateKey() { return key_.key_value(); }

  // Generates a new KeyPair instance containing an ed25519 key pair.
  static std::unique_ptr<KeyPair> Generate();

  // Creates a KeyPair instance from a raw unencrypted PKCS#8 encoded private key. A PKCS#8 encoded
  // string containing both the 32-byte private key (or seed), and the corresponding 32-byte public
  // key is expected.
  static std::unique_ptr<KeyPair> FromPkcs8(const std::string& pkcs8_private_key);

 private:
  Ed25519PrivateKey key_;
  KeyPair(const Ed25519PrivateKey private_key) : key_(private_key) {}
};

// Computes the sha256 hash of the unhashed input string. Returns true if hashing is successful. In
// this case the hashed value is stored in the second input parameter as an octet string.
bool compute_sha256_hash(const std::string& unhashed, std::string& hashed);

}  // namespace oak

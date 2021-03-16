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

#include <memory>
#include <string>
#include <vector>

#include "absl/base/attributes.h"

namespace oak {

// Implementation of the unencrypted PKCS#8 private key encoding:
// https://tools.ietf.org/html/rfc5208. This implementation is based on the PKCS#8 implementation in
// the Rust ring crate (https://crates.io/crates/ring).
namespace pkcs8 {

class ByteArray {
 public:
  ByteArray(const std::string& in_string);
  ByteArray(unsigned char* in_bytes, int in_len);
  std::string ToString();
  std::string ToBase64();
  static ByteArray FromBase64(const std::string& in_string);

  unsigned char* bytes;
  int len;
};

// Represents private key information that can be encoded as PKCS#8. Public key may be empty. The
// standard also allows atributes, but this implementation omits that. The public key algorithm is
// also omitted. That information is encapsulated in struct `Template`.
struct PrivateKeyInfo {
  ByteArray private_key;
  ByteArray public_key;
};

// This is a simplified version of the pkcs8 `Template` class in the Rust ring crate.
struct Template {
  // Byte array representing the template for generating the desired PKCS#8 encoding.
  ByteArray bytes;

  // Version
  int version;

  // `bytes` will be split into two parts at `private_key_index`, where the
  // first part is written before the private key and the second part is
  // written after the private key. The public key is written after the
  // second part.
  int private_key_index;

  // Length of  the private key. This is needed for decoding the PKCS#8 documents.
  int private_key_len;
};

// Encode the given private and public key, wrapped in a PrivateKeyInfo object, as a PKCS#8 encoded
// ByteArray, using the given template.
std::unique_ptr<ByteArray> to_pkcs8(const PrivateKeyInfo& data, const Template& pkcs8_template);

// Extract private key info from a PKCS#8 encoded private key, using the given template.
PrivateKeyInfo from_pkcs8(const ByteArray& pkcs_str, const Template& pkcs8_template);

// Template for serializing and deserializing Ed25519 keys as unencrypted PKCS#8 byte arrays, as
// specified in [RFC5208](https://tools.ietf.org/html/rfc5208).
//
// See also https://tools.ietf.org/html/rfc8410 for algorithm identifiers.
// NOTE: Cannot use ABSL_CONST_INIT because ByteArray (a field in Template) does not have a
// constexpr constructor.
extern const Template kEd25519Pkcs8Template;

}  // namespace pkcs8
}  // namespace oak

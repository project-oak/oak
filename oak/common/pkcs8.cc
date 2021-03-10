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

#include "oak/common/pkcs8.h"

#include <cstring>

#include "absl/strings/escaping.h"
#include "glog/logging.h"

namespace oak {

namespace pkcs8 {

// Template of the form |prefix|middle| for serializing and deserializing Ed25519 keys as
// unencrypted PKCS#8 byte arrays. With this template, the 32-byte
// private key (or seed) will be placed after the `prefix`, and the 32-byte public key will be
// inserted at the end, resulting in |prefix|private-key|middle|public-key|. With this tempplate,
// no additional attributes can be included in the encoded byte array. This tempplate should be used
// in combination with `kEd25519Pkcs8Template`, which specifies the location of the split between
// `prefix` and `middle`.
//
// This is copied from the Rust ring crate
// https://github.com/briansmith/ring/blob/main/src/ec/curve25519/ed25519/ed25519_pkcs8_v2_template.der.
const char kBase64Ed25519Pkcs8Templace[] = "MFMCAQEwBQYDK2VwBCIEIKEjAyEA";

// Encapsulates the template byte array, the version (for convenience), and the index at which the
// template should be split into `prefix` and `middle`.
const Template kEd25519Pkcs8Template{ByteArray::FromBase64(kBase64Ed25519Pkcs8Templace), 1, 16, 32};

ByteArray::ByteArray(unsigned char* in_bytes, int in_len) {
  bytes = new unsigned char[in_len];
  std::memcpy(bytes, in_bytes, in_len);
  len = in_len;
}

ByteArray::ByteArray(const std::string& in_string) {
  char* buffer = new char[in_string.length()];
  std::memcpy(buffer, in_string.data(), in_string.length());
  bytes = reinterpret_cast<unsigned char*>(buffer);
  len = in_string.length();
}

ByteArray ByteArray::FromBase64(const std::string& in_string) {
  std::string buffer;
  if (!absl::Base64Unescape(in_string, &buffer)) {
    LOG(FATAL) << "Couldn't decode Base64 input";
  }
  ByteArray byte_array(buffer);
  return byte_array;
}

std::string ByteArray::ToBase64() {
  std::string buffer = ToString();
  return absl::Base64Escape(buffer);
}

std::string ByteArray::ToString() {
  std::string buffer(std::string(reinterpret_cast<char const*>(bytes), len));
  return buffer;
}

// Splits the bytes in the given template at the `private_key_index` into `|prefix|middle|`. Inserts
// the private key and the public key to form `|prefix|private-key|middle|public-key|`.
std::unique_ptr<ByteArray> to_pkcs8(const PrivateKeyInfo& data, const Template& pkcs8_template) {
  if (pkcs8_template.private_key_len != data.private_key.len) {
    LOG(FATAL) << "The length of the given private key does not match the length expected in the "
                  "template.";
  }
  int len = pkcs8_template.bytes.len + data.private_key.len + data.public_key.len;
  unsigned char* bytes = new unsigned char[len];

  // copy `prefix` from template to bytes: |prefix|
  std::memcpy(&bytes[0], pkcs8_template.bytes.bytes, pkcs8_template.private_key_index);

  // copy private key to bytes: |prefix|private-key|
  std::memcpy(&bytes[pkcs8_template.private_key_index], data.private_key.bytes,
              data.private_key.len);

  // copy `middle` from template to bytes: |prefix|private-key|middle|
  int middle_len = pkcs8_template.bytes.len - pkcs8_template.private_key_index;
  std::memcpy(&bytes[pkcs8_template.private_key_index + data.private_key.len],
              &pkcs8_template.bytes.bytes[pkcs8_template.private_key_index], middle_len);

  // copy public key to bytes: |prefix|private-key|middle|public-key|
  std::memcpy(&bytes[pkcs8_template.bytes.len + data.private_key.len], data.public_key.bytes,
              data.public_key.len);

  std::unique_ptr<ByteArray> byte_array(new ByteArray(bytes, len));
  delete[] bytes;
  return byte_array;
}

// Splits the bytes in the given template at the `private_key_index` into `|e_prefix|e_middle|`.
// Then using the template, splits the input array at `private_key_index` and `private_key_index +
// private_key_len` into |a_prefix|private-key|a_middle|public-key|. If `e_prefix` and `a_prefix`
// match, and `e_middle` and `a_middle` match, returns the private and public keys in a
// PrivateKeyInfo object.
PrivateKeyInfo from_pkcs8(const ByteArray& pkcs_str, const Template& pkcs8_template) {
  // Template `prefix` check
  if (std::memcmp(&pkcs_str.bytes[0], &pkcs8_template.bytes.bytes[0],
                  pkcs8_template.private_key_index) != 0) {
    LOG(FATAL) << "PKCS#8 template prefix mismatch.";
  }

  // Template `middle` check
  int middle_ind = pkcs8_template.private_key_index + pkcs8_template.private_key_len;
  int middle_len = pkcs8_template.bytes.len - pkcs8_template.private_key_index;
  if (std::memcmp(&pkcs_str.bytes[middle_ind],
                  &pkcs8_template.bytes.bytes[pkcs8_template.private_key_index], middle_len) != 0) {
    LOG(FATAL) << "PKCS#8 template middle mismatch.";
  }

  // Extract private key and public key values
  int public_key_len = pkcs_str.len - pkcs8_template.bytes.len - pkcs8_template.private_key_len;
  int public_key_index = pkcs8_template.bytes.len + pkcs8_template.private_key_len;
  PrivateKeyInfo p{
      ByteArray(&pkcs_str.bytes[pkcs8_template.private_key_index], pkcs8_template.private_key_len),
      ByteArray(&pkcs_str.bytes[public_key_index], public_key_len)};
  return p;
}

}  // namespace pkcs8

}  // namespace oak

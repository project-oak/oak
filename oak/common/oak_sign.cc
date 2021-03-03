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

#include "oak/common/oak_sign.h"

#include <openssl/base.h>
#include <openssl/bytestring.h>
#include <openssl/curve25519.h>
#include <openssl/evp.h>
#include <openssl/pkcs8.h>

#include <map>
#include <sstream>

#include "absl/strings/escaping.h"
#include "glog/logging.h"
#include "oak/common/utils.h"

struct Bytes {
  uint8_t* data;
  unsigned int length;
};
bool compute_base64_hash(const std::string& unhashed, std::string& base64_hash);
std::string bytes_to_base64(uint8_t* bytes, unsigned int length);
Bytes base64_to_bytes(std::string& base64);

namespace oak {

void generate(const std::string& private_key_path, const std::string& public_key_path) {
  uint8_t public_key[32], private_key[64];
  ED25519_keypair(public_key, private_key);

  std::stringstream pub_ss;
  for (unsigned int i = 0; i < 32; ++i) {
    pub_ss << (char)public_key[i];
  }
  std::map<std::string, std::string> pub_map;
  pub_map["PUBLIC KEY"] = absl::Base64Escape(pub_ss.str());
  oak::utils::write_pem(pub_map, public_key_path);

  std::stringstream pri_ss;
  for (unsigned int i = 0; i < 64; ++i) {
    pri_ss << (char)private_key[i];
  }
  std::map<std::string, std::string> pri_map;
  pri_map["PRIVATE KEY"] = absl::Base64Escape(pri_ss.str());
  oak::utils::write_pem(pri_map, private_key_path);
}

// TODO(#1851): Compute public key from the private key, and store everything in file.
std::string sign(const std::string& private_key_path, const std::string& input_string) {
  auto pem_map = oak::utils::read_pem(private_key_path);

  // Read base64 private key from file and decode it
  Bytes private_key;
  if (pem_map.find("PRIVATE KEY") == pem_map.end()) {
    LOG(FATAL) << "No private key in the pem file";
  } else {
    private_key = base64_to_bytes(pem_map["PRIVATE KEY"]);
  }

  // Compute base64-encoded hash of the input string
  std::string base64_hash;
  if (!compute_base64_hash(input_string, base64_hash)) {
    LOG(FATAL) << "Failed to compute base64-encoded hash.";
  }
  // Decode hash into byte array
  Bytes hash_bytes = base64_to_bytes(base64_hash);

  // Compute signature for the hash
  uint8_t signature[64];
  if (!ED25519_sign(signature, hash_bytes.data, hash_bytes.length, private_key.data)) {
    LOG(FATAL) << "Failed to sign the message";
  }

  delete[] private_key.data;
  delete[] hash_bytes.data;

  // Get base64 encoding of the signature
  return bytes_to_base64(signature, 64);

  // TODO(#1851): Uncomment when this method can derive public key from the private key and write
  // everything to file.

  // write to file
  //   std::map<std::string, std::string> map;
  //   map["PUBLIC KEY"] = base64_public_key;
  //   map["SIGNATURE"] = base64_signature;
  //   map["HASH"] = base64_hash;
  //   oak::utils::write_pem(map, signature_file);
}

}  // namespace oak

bool compute_base64_hash(const std::string& unhashed, std::string& base64_hash) {
  bool success = false;

  EVP_MD_CTX* context = EVP_MD_CTX_new();

  if (context != NULL) {
    if (EVP_DigestInit_ex(context, EVP_sha256(), NULL)) {
      if (EVP_DigestUpdate(context, unhashed.c_str(), unhashed.length())) {
        uint8_t hash[EVP_MAX_MD_SIZE];
        unsigned int lengthOfHash = 0;

        if (EVP_DigestFinal_ex(context, hash, &lengthOfHash)) {
          base64_hash = bytes_to_base64(hash, lengthOfHash);
          success = true;
        }
      }
    }

    EVP_MD_CTX_free(context);
  }

  return success;
}

std::string bytes_to_base64(uint8_t* bytes, unsigned int length) {
  std::stringstream ss;
  for (unsigned int i = 0; i < length; ++i) {
    ss << (char)bytes[i];
  }
  return absl::Base64Escape(ss.str());
}

Bytes base64_to_bytes(std::string& base64) {
  std::string decoded_val;
  if (!absl::Base64Unescape(base64, &decoded_val)) {
    LOG(FATAL) << "Failed to decode base64.";
  }
  Bytes bytes;
  bytes.data = new uint8_t[decoded_val.length()];
  memcpy(bytes.data, decoded_val.data(), decoded_val.length());
  bytes.length = decoded_val.length();

  return bytes;
}

// TODO(#1851): Fix this
// std::string derive_public_key_from_private_key(Bytes private_key) {
//   // Compute public key from the private key
//   CBS pri_key;
//   CBS_init(&pri_key, private_key.data, private_key.length);
//   EVP_PKEY* pkey = PKCS8_parse_encrypted_private_key(&pri_key, NULL, 0);

//   // Get base64 encoding of the public key
//   if (pkey == NULL || EVP_PKEY_id(pkey) != EVP_PKEY_EC) {
//     LOG(FATAL) << "Failed to parse private key.";
//   }
//   const EC_POINT* pub = EC_KEY_get0_public_key(pkey->pkey.ec);

//   BIGNUM* x = BN_new();
//   BIGNUM* y = BN_new();

//   if (!EC_POINT_get_affine_coordinates_GFp(EC_KEY_get0_group(pkey->pkey.ec), pub, x, y, NULL)) {
//     LOG(FATAL) << "Failed to get public key.";
//   }

//   uint8_t* public_key;
//   int len = BN_bn2bin(x, public_key);
//   return bytes_to_base64(public_key, len);
// }

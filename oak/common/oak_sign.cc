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
#include "tink/signature/ed25519_sign_key_manager.h"
#include "tink/subtle/ed25519_verify_boringssl.h"
#include "tink/util/istream_input_stream.h"

using crypto::tink::Ed25519SignKeyManager;
using ::crypto::tink::util::StatusOr;
using ::google::crypto::tink::Ed25519KeyFormat;
using ::google::crypto::tink::Ed25519PrivateKey;
using ::google::crypto::tink::Ed25519PublicKey;

bool compute_sha256_hash(const std::string& unhashed, std::string& hashed);
namespace oak {

std::string generate() {
  StatusOr<Ed25519PrivateKey> key_or = Ed25519SignKeyManager().CreateKey(Ed25519KeyFormat());
  if (!key_or.ok()) {
    LOG(FATAL) << "Could not generate Ed25519 key pair";
  }
  Ed25519PrivateKey key = key_or.ValueOrDie();

  return key.key_value();
}

void store_private_key(const std::string& private_key, const std::string& private_key_path) {
  std::map<std::string, std::string> pri_map;
  pri_map["PRIVATE KEY"] = absl::Base64Escape(private_key);
  oak::utils::write_pem(pri_map, private_key_path);
}

oak::identity::SignedChallenge sign(const std::string& private_key,
                                    const std::string& input_string) {
  Ed25519KeyFormat format;

  crypto::tink::util::IstreamInputStream input_stream{
      absl::make_unique<std::stringstream>(private_key)};

  StatusOr<Ed25519PrivateKey> key_or = Ed25519SignKeyManager().DeriveKey(format, &input_stream);
  if (!key_or.ok()) {
    LOG(FATAL) << "Couldn't derive keys from the given private key";
  }
  Ed25519PrivateKey key = key_or.ValueOrDie();

  auto signer_or = Ed25519SignKeyManager().GetPrimitive<crypto::tink::PublicKeySign>(key);

  // Compute sha256 hash of the input string
  std::string hash_value;
  if (!compute_sha256_hash(input_string, hash_value)) {
    LOG(FATAL) << "Failed to compute sha256 hash.";
  }
  std::string signed_hash = signer_or.ValueOrDie()->Sign(hash_value).ValueOrDie();

  oak::identity::SignedChallenge signed_challenge;
  signed_challenge.set_signed_hash(signed_hash);
  signed_challenge.set_public_key(key_or.ValueOrDie().public_key().key_value());

  return signed_challenge;
}

}  // namespace oak

bool compute_sha256_hash(const std::string& unhashed, std::string& hashed) {
  bool success = false;

  EVP_MD_CTX* context = EVP_MD_CTX_new();

  if (context != NULL) {
    if (EVP_DigestInit_ex(context, EVP_sha256(), NULL)) {
      if (EVP_DigestUpdate(context, unhashed.c_str(), unhashed.length())) {
        uint8_t hash[EVP_MAX_MD_SIZE];
        unsigned int lengthOfHash = 0;

        if (EVP_DigestFinal_ex(context, hash, &lengthOfHash)) {
          std::stringstream ss;
          for (unsigned int i = 0; i < lengthOfHash; ++i) {
            ss << (char)hash[i];
          }
          hashed = ss.str();
          success = true;
        }
      }
    }

    EVP_MD_CTX_free(context);
  }

  return success;
}

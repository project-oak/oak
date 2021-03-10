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

#include "glog/logging.h"
#include "oak/common/utils.h"
#include "tink/subtle/ed25519_verify_boringssl.h"
#include "tink/subtle/subtle_util_boringssl.h"
#include "tink/util/istream_input_stream.h"

using ::crypto::tink::Ed25519SignKeyManager;
using ::crypto::tink::subtle::HashType;
using ::crypto::tink::subtle::SubtleUtilBoringSSL;
using ::crypto::tink::subtle::boringssl::ComputeHash;
using ::crypto::tink::util::StatusOr;
using ::google::crypto::tink::Ed25519KeyFormat;
using ::google::crypto::tink::Ed25519PrivateKey;
using ::google::crypto::tink::Ed25519PublicKey;

namespace oak {
const char kPrivateKeyPemTag[] = "PRIVATE KEY";

Ed25519PrivateKey parse_key(const std::string& private_key) {
  // Retrieve private and public keys from the input private key string
  crypto::tink::util::IstreamInputStream input_stream(
      absl::make_unique<std::stringstream>(private_key));

  StatusOr<Ed25519PrivateKey> key_or =
      Ed25519SignKeyManager().DeriveKey(Ed25519KeyFormat(), &input_stream);
  if (!key_or.ok()) {
    LOG(FATAL) << "Couldn't derive keys from the given private key";
  }
  Ed25519PrivateKey key = key_or.ValueOrDie();
  return key;
}

KeyPair::KeyPair(const std::string& private_key) : KeyPair(parse_key(private_key)) {}

std::unique_ptr<KeyPair> KeyPair::Generate() {
  StatusOr<Ed25519PrivateKey> key_or = Ed25519SignKeyManager().CreateKey(Ed25519KeyFormat());
  if (!key_or.ok()) {
    LOG(FATAL) << "Could not generate Ed25519 key pair";
  }
  Ed25519PrivateKey key = key_or.ValueOrDie();
  std::unique_ptr<KeyPair> key_pair(new KeyPair(key));
  return key_pair;
}

Signature KeyPair::Sign(const std::string& message) {
  // Compute sha256 hash of the input string
  std::string hash_value;
  if (!compute_sha256_hash(message, hash_value)) {
    LOG(FATAL) << "Failed to compute sha256 hash.";
  }

  // Sign the hash with the private key
  auto signer_or = Ed25519SignKeyManager().GetPrimitive<crypto::tink::PublicKeySign>(key_);
  std::string signed_hash = signer_or.ValueOrDie()->Sign(hash_value).ValueOrDie();

  Signature signature;
  signature.signed_hash = signed_hash;
  signature.public_key = key_.public_key().key_value();

  return signature;
}

bool compute_sha256_hash(const std::string& unhashed, std::string& hashed) {
  StatusOr<const EVP_MD*> res = SubtleUtilBoringSSL::EvpHash(HashType::SHA256);
  const EVP_MD* evp_sha256 = res.ValueOrDie();
  auto digest_result = ComputeHash(unhashed, *evp_sha256);
  if (!digest_result.ok()) {
    return false;
  }
  auto digest = digest_result.ValueOrDie();
  unsigned char* hash = digest.data();
  hashed = std::string(reinterpret_cast<char const*>(hash), digest.size());
  return true;
}

}  // namespace oak

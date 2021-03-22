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

#include "absl/strings/escaping.h"
#include "glog/logging.h"
#include "oak/common/pkcs8.h"
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
using oak::pkcs8::PrivateKeyInfo;

namespace oak {
const char kPrivateKeyPemTag[] = "PRIVATE KEY";

// Creates an Ed25519PrivateKey instance from the raw PKCS#8 encoded input private key.
Ed25519PrivateKey parse_pkcs8(const std::string& pkcs8_private_key) {
  oak::pkcs8::PrivateKeyInfo key_info =
      oak::pkcs8::from_pkcs8(pkcs8_private_key, oak::pkcs8::kEd25519Pkcs8Template);

  int version = oak::pkcs8::kEd25519Pkcs8Template.version;
  Ed25519PrivateKey ed25519_key;
  ed25519_key.set_version(version);
  ed25519_key.set_key_value(key_info.private_key);

  auto public_key = ed25519_key.mutable_public_key();
  public_key->set_version(version);
  public_key->set_key_value(key_info.public_key);

  return ed25519_key;
}

std::unique_ptr<KeyPair> KeyPair::Generate() {
  StatusOr<Ed25519PrivateKey> key_or = Ed25519SignKeyManager().CreateKey(Ed25519KeyFormat());
  if (!key_or.ok()) {
    LOG(FATAL) << "Could not generate Ed25519 key pair";
  }
  Ed25519PrivateKey key = key_or.ValueOrDie();
  std::unique_ptr<KeyPair> key_pair(new KeyPair(key));
  return key_pair;
}

std::unique_ptr<KeyPair> KeyPair::FromPkcs8(const std::string& pkcs8_private_key) {
  Ed25519PrivateKey key = parse_pkcs8(pkcs8_private_key);
  std::unique_ptr<KeyPair> key_pair(new KeyPair(key));
  return key_pair;
}

std::string KeyPair::ToPkcs8() {
  oak::pkcs8::PrivateKeyInfo pk_info{GetPrivateKey(), GetPublicKeyRaw()};
  std::string pkcs8_encoded = oak::pkcs8::to_pkcs8(pk_info, oak::pkcs8::kEd25519Pkcs8Template);
  return pkcs8_encoded;
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
  signature.public_key_der = this->GetPublicKeyDer();

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

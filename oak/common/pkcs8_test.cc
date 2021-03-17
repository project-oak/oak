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

#include "absl/strings/escaping.h"
#include "glog/logging.h"
#include "gtest/gtest.h"

namespace oak {
namespace pkcs8 {

// Private key (seed) extracted from oak/examples/keys/ed25519/test.key
const char* BASE64_PRIVATE_KEY = "6xCAYryn1U8t6fY7cMP99e8XcvLBvEzfavhx4/tfOUc=";
// Public key from oak/examples/keys/ed25519/test.pub
const char* BASE64_PUBLIC_KEY = "f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=";
// PKCS#8 formatted private key info from oak/examples/keys/ed25519/test.key
const char* BASE64_PKCS8 =
    "MFMCAQEwBQYDK2VwBCIEIOsQgGK8p9VPLen2O3DD/fXvF3LywbxM32r4ceP7XzlHoSMDIQB/jVIKU21HiLjq/"
    "ZO6HV9Atu39mpGvWUQ1qMJb3aPI/g==";

TEST(Pkcs8Test, EncodeKeyPair) {
  std::string decoded_public_key;
  if (!absl::Base64Unescape(BASE64_PUBLIC_KEY, &decoded_public_key)) {
    LOG(FATAL) << "Couldn't decode Base64 input";
  }

  std::string decoded_private_key;
  if (!absl::Base64Unescape(BASE64_PRIVATE_KEY, &decoded_private_key)) {
    LOG(FATAL) << "Couldn't decode Base64 input";
  }

  ASSERT_EQ(decoded_private_key.length(), 32);
  ASSERT_EQ(decoded_public_key.length(), 32);
  ASSERT_EQ(kEd25519Pkcs8Template.bytes.length(), 21);

  PrivateKeyInfo pk_info{decoded_private_key, decoded_public_key};
  std::string pkcs8 = to_pkcs8(pk_info, kEd25519Pkcs8Template);
  ASSERT_EQ(pkcs8.length(), 85);
  ASSERT_EQ(absl::Base64Escape(pkcs8), BASE64_PKCS8);
}

TEST(Pkcs8Test, DecodePkcs8) {
  std::string decoded_pkcs8;
  if (!absl::Base64Unescape(BASE64_PKCS8, &decoded_pkcs8)) {
    LOG(FATAL) << "Couldn't decode Base64 input";
  }

  PrivateKeyInfo pk_info = from_pkcs8(decoded_pkcs8, kEd25519Pkcs8Template);

  ASSERT_EQ(absl::Base64Escape(pk_info.private_key), BASE64_PRIVATE_KEY);
  ASSERT_EQ(absl::Base64Escape(pk_info.public_key), BASE64_PUBLIC_KEY);
}
}  // namespace pkcs8
}  // namespace oak

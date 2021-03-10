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

TEST(Pkcs8Test, ByteArrayFromToBase64) {
  ByteArray public_key = ByteArray::FromBase64(BASE64_PUBLIC_KEY);
  ASSERT_EQ(public_key.len, 32);
  ASSERT_EQ(public_key.ToBase64(), BASE64_PUBLIC_KEY);
}

TEST(Pkcs8Test, EncodeKeyPair) {
  ByteArray public_key = ByteArray::FromBase64(BASE64_PUBLIC_KEY);
  ByteArray private_key = ByteArray::FromBase64(BASE64_PRIVATE_KEY);
  ASSERT_EQ(private_key.len, 32);
  ASSERT_EQ(public_key.len, 32);
  ASSERT_EQ(kEd25519Pkcs8Template.bytes.len, 21);

  PrivateKeyInfo pk_info{private_key, public_key};
  std::unique_ptr<ByteArray> ba = to_pkcs8(pk_info, kEd25519Pkcs8Template);
  ASSERT_EQ(ba->len, 85);
  ASSERT_EQ(ba->ToBase64(), BASE64_PKCS8);
}

TEST(Pkcs8Test, DecodePkcs8) {
  ByteArray private_key = ByteArray::FromBase64(BASE64_PKCS8);
  PrivateKeyInfo pk_info = from_pkcs8(private_key, kEd25519Pkcs8Template);

  ASSERT_EQ(pk_info.private_key.ToBase64(), BASE64_PRIVATE_KEY);
  ASSERT_EQ(pk_info.public_key.ToBase64(), BASE64_PUBLIC_KEY);
}
}  // namespace pkcs8
}  // namespace oak

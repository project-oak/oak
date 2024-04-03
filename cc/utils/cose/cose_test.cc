/*
 * Copyright 2024 The Project Oak Authors
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

#include "cc/utils/cose/cose.h"

#include <cstdint>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::utils::cose {
namespace {

using ::testing::ElementsAreArray;

TEST(CoseTest, CoseSign1SerializeDeserializeSuccess) {
  std::vector<uint8_t> test_payload = {1, 2, 3, 4};
  auto serialized_cose_sign1 = CoseSign1::Serialize(test_payload);
  EXPECT_TRUE(serialized_cose_sign1.ok()) << serialized_cose_sign1.status();
  auto serialized_cose_sign1_string =
      std::string(serialized_cose_sign1->begin(), serialized_cose_sign1->end());

  auto deserialized_cose_sign1 =
      CoseSign1::Deserialize(serialized_cose_sign1_string);
  EXPECT_TRUE(deserialized_cose_sign1.ok()) << deserialized_cose_sign1.status();
  EXPECT_THAT(deserialized_cose_sign1->payload->value(),
              ElementsAreArray(test_payload));
}

TEST(CoseTest, CoseKeySerializeDeserializeSuccess) {
  std::vector<uint8_t> test_public_key = {1, 2, 3, 4};
  auto serialized_cose_key = CoseKey::SerializeHpkePublicKey(test_public_key);
  EXPECT_TRUE(serialized_cose_key.ok()) << serialized_cose_key.status();

  auto deserialized_cose_key =
      CoseKey::DeserializeHpkePublicKey(*serialized_cose_key);
  EXPECT_TRUE(deserialized_cose_key.ok()) << deserialized_cose_key.status();
  EXPECT_THAT(deserialized_cose_key->GetPublicKey(),
              ElementsAreArray(test_public_key));
}

}  // namespace
}  // namespace oak::utils::cose

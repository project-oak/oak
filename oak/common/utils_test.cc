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

#include "oak/common/utils.h"

#include "gtest/gtest.h"

namespace oak {
namespace utils {

const std::string PEM_ENCODED = "-----BEGIN KEY 1-----\nVkFMIDE=\n-----END KEY 1-----\n\n";

// Check that data is correctly encoded as PEM.
TEST(UtilsTest, EncodePem) {
  std::map<std::string, std::string> in_map{
      {"KEY 1", "VAL 1"},
  };
  auto pem_encoded = encode_pem(in_map);
  ASSERT_EQ(pem_encoded, PEM_ENCODED);
}

// Check that PEM encoded data is correctly decoded.
TEST(UtilsTest, DecodePem) {
  auto out_map = decode_pem(PEM_ENCODED);
  ASSERT_EQ(out_map["KEY 1"], "VAL 1");
}

}  // namespace utils
}  // namespace oak

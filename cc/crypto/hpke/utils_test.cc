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

#include "cc/crypto/hpke/utils.h"

#include <cstdint>

#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::crypto {
namespace {

using ::testing::ContainerEq;
using ::testing::Not;

TEST(RecipientContextTest, GenerateRandomNonceReturnsDifferentValues) {
  absl::StatusOr<const std::vector<uint8_t>> nonce1 = GenerateRandomNonce();
  ASSERT_TRUE(nonce1.ok());

  absl::StatusOr<const std::vector<uint8_t>> nonce2 = GenerateRandomNonce();
  ASSERT_TRUE(nonce2.ok());

  EXPECT_THAT(*nonce1, Not(ContainerEq(*nonce2)));
}

}  // namespace
}  // namespace oak::crypto

/*
 * Copyright 2026 The Project Oak Authors
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

#include "cc/crypto/tink/signature/ml_dsa_44_utils.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::crypto::tink {
namespace {

using ::absl_testing::IsOk;
using ::absl_testing::StatusIs;

TEST(MlDsa44UtilsTest, GenerateKeyPairProducesValidKeyLengths) {
  absl::StatusOr<MlDsa44KeyPair> key_pair = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair, IsOk());
  EXPECT_EQ(key_pair->public_key.size(), 1312);
  EXPECT_FALSE(key_pair->private_key.empty());
}

TEST(MlDsa44UtilsTest, SignAndVerifyRoundTrip) {
  absl::StatusOr<MlDsa44KeyPair> key_pair = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair, IsOk());

  const std::string message = "test message for ML-DSA-44 round trip";
  absl::StatusOr<std::string> signature = SignMlDsa44(message, *key_pair);
  ASSERT_THAT(signature, IsOk());
  EXPECT_EQ(signature->size(), 2420);

  EXPECT_THAT(VerifyMlDsa44(message, *signature, key_pair->public_key), IsOk());
}

TEST(MlDsa44UtilsTest, VerifyRejectsWrongMessage) {
  absl::StatusOr<MlDsa44KeyPair> key_pair = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair, IsOk());

  const std::string message = "original message";
  absl::StatusOr<std::string> signature = SignMlDsa44(message, *key_pair);
  ASSERT_THAT(signature, IsOk());

  EXPECT_THAT(
      VerifyMlDsa44("different message", *signature, key_pair->public_key),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(MlDsa44UtilsTest, VerifyRejectsWrongKey) {
  absl::StatusOr<MlDsa44KeyPair> key_pair_1 = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair_1, IsOk());
  absl::StatusOr<MlDsa44KeyPair> key_pair_2 = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair_2, IsOk());

  const std::string message = "signed by key_pair_1";
  absl::StatusOr<std::string> signature = SignMlDsa44(message, *key_pair_1);
  ASSERT_THAT(signature, IsOk());

  // Verify with a different key should fail.
  EXPECT_THAT(VerifyMlDsa44(message, *signature, key_pair_2->public_key),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(MlDsa44UtilsTest, TwoKeyPairsAreDifferent) {
  absl::StatusOr<MlDsa44KeyPair> key_pair_1 = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair_1, IsOk());
  absl::StatusOr<MlDsa44KeyPair> key_pair_2 = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair_2, IsOk());

  EXPECT_NE(key_pair_1->public_key, key_pair_2->public_key);
  EXPECT_NE(key_pair_1->private_key, key_pair_2->private_key);
}

TEST(MlDsa44UtilsTest, VerifyRejectsMutatedSignature) {
  absl::StatusOr<MlDsa44KeyPair> key_pair = GenerateMlDsa44KeyPair();
  ASSERT_THAT(key_pair, IsOk());

  const std::string message = "test message for mutation check";
  absl::StatusOr<std::string> signature = SignMlDsa44(message, *key_pair);
  ASSERT_THAT(signature, IsOk());

  // Flip a byte in the middle of the signature.
  std::string mutated_signature = *signature;
  mutated_signature[mutated_signature.size() / 2] ^= 0xFF;

  EXPECT_THAT(VerifyMlDsa44(message, mutated_signature, key_pair->public_key),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(MlDsa44UtilsTest, VerifyRejectsInvalidPublicKey) {
  const std::string bad_key = "too short";
  const std::string message = "hello";
  const std::string fake_sig(2420, '\0');

  EXPECT_THAT(VerifyMlDsa44(message, fake_sig, bad_key),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace oak::crypto::tink

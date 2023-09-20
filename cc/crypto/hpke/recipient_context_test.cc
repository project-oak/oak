/*
 * Copyright 2023 The Project Oak Authors
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

#include "cc/crypto/hpke/recipient_context.h"

#include "absl/status/statusor.h"
#include "cc/crypto/hpke/sender_context.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "openssl/hpke.h"

namespace oak::crypto {
namespace {

using ::testing::StrEq;
using ::testing::StrNe;

class RecipientContextTest : public testing::Test {
 protected:
  void SetUp() override {
    // This key pairing was randomly generated using EVP_HPKE_KEY_generate() with the x25519 KEM.
    const std::vector<uint8_t> public_key_bytes = {
        236, 102, 18, 92,  231, 237, 92, 56, 199, 21,  200, 213, 172, 150, 80, 217,
        64,  33,  77, 203, 109, 68,  21, 12, 76,  219, 16,  62,  110, 19,  69, 8};
    std::string serialized_public_key(public_key_bytes.begin(), public_key_bytes.end());
    const std::vector<uint8_t> private_key_bytes = {
        255, 12,  169, 64, 221, 170, 194, 165, 224, 77,  222, 165, 95, 179, 124, 55,
        236, 237, 58,  11, 130, 177, 153, 40,  31,  221, 13,  138, 71, 107, 243, 173};
    std::string serialized_private_key(private_key_bytes.begin(), private_key_bytes.end());
    recipient_key_pair_.public_key = serialized_public_key;
    recipient_key_pair_.private_key = serialized_private_key;

    // Random encapsulated public key from the SetupBaseSender function.
    const std::vector<uint8_t> encap_public_key_bytes = {
        85,  255, 224, 169, 132, 101, 176, 248, 95,  67, 86,  31, 44, 31, 230, 224,
        226, 174, 242, 10,  200, 162, 222, 196, 255, 25, 114, 64, 4,  15, 193, 89};
    std::string encap_public_key_string(encap_public_key_bytes.begin(),
                                        encap_public_key_bytes.end());
    encap_public_key_ = encap_public_key_string;

    info_string_ = "Test HPKE info";
    associated_data_response_ = "Test response associated data";
    associated_data_request_ = "Test request associated data";
  }
  KeyPair recipient_key_pair_;
  std::string encap_public_key_;
  std::string info_string_;
  std::string associated_data_response_;
  std::string associated_data_request_;
};

TEST_F(RecipientContextTest, SetupBaseRecipientEmptyEncapKeyReturnsFailure) {
  std::string empty_string = "";
  auto recipient_context = SetupBaseRecipient(empty_string, recipient_key_pair_, info_string_);
  EXPECT_FALSE(recipient_context.ok());
}

TEST_F(RecipientContextTest, SetupBaseRecipientEmptyPublicKeyReturnsFailure) {
  recipient_key_pair_.public_key = "";
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  EXPECT_FALSE(recipient_context.ok());
}

TEST_F(RecipientContextTest, SetupBaseRecipientEmptyPrivateKeyReturnsFailure) {
  recipient_key_pair_.private_key = "";
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  EXPECT_FALSE(recipient_context.ok());
}

TEST_F(RecipientContextTest, SetupBaseRecipientMismatchedKeyPairReturnsFailure) {
  // We edit the default public key to produce an invalid key pairing.
  std::vector<uint8_t> different_public_key(recipient_key_pair_.public_key.begin(),
                                            recipient_key_pair_.public_key.end());
  different_public_key[0] += 1;
  std::string different_public_key_str(different_public_key.begin(), different_public_key.end());
  recipient_key_pair_.public_key = different_public_key_str;
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  EXPECT_FALSE(recipient_context.ok());
}

TEST_F(RecipientContextTest, SetupBaseRecipientReturnsValidPointersOnSuccess) {
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  ASSERT_TRUE(recipient_context.ok());
  EXPECT_TRUE(*recipient_context);
}

TEST_F(RecipientContextTest, RecipientContextOpenSuccess) {
  // Initialize an HPKE sender.
  auto sender_context = SetupBaseSender(recipient_key_pair_.public_key, info_string_);
  ASSERT_TRUE(sender_context.ok());

  std::string plaintext = "Hello World";

  auto ciphertext = (*sender_context)->Seal(plaintext, associated_data_request_);
  ASSERT_TRUE(ciphertext.ok());

  std::string encap_public_key = (*sender_context)->GetSerializedEncapsulatedPublicKey();
  auto recipient_context = SetupBaseRecipient(encap_public_key, recipient_key_pair_, info_string_);
  ASSERT_TRUE(recipient_context.ok());
  auto received_plaintext = (*recipient_context)->Open(*ciphertext, associated_data_request_);
  ASSERT_TRUE(received_plaintext.ok());

  EXPECT_THAT(*received_plaintext, StrEq(plaintext));
}

TEST_F(RecipientContextTest, RecipientRequestContextOpenFailure) {
  // Initialize an HPKE sender.
  auto sender_context = SetupBaseSender(recipient_key_pair_.public_key, info_string_);
  ASSERT_TRUE(sender_context.ok());

  std::string plaintext = "Hello World";

  auto ciphertext = (*sender_context)->Seal(plaintext, associated_data_request_);
  ASSERT_TRUE(ciphertext.ok());

  std::string edited_ciphertext = absl::StrCat(*ciphertext, "no!");

  std::string encap_public_key = (*sender_context)->GetSerializedEncapsulatedPublicKey();
  auto recipient_context = SetupBaseRecipient(encap_public_key, recipient_key_pair_, info_string_);
  ASSERT_TRUE(recipient_context.ok());

  auto received_plaintext = (*recipient_context)->Open(edited_ciphertext, associated_data_request_);
  EXPECT_FALSE(received_plaintext.ok());
  EXPECT_EQ(received_plaintext.status().code(), absl::StatusCode::kAborted);
}

TEST_F(RecipientContextTest, RecipientResponseContextSealSuccess) {
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  ASSERT_TRUE(recipient_context.ok());

  std::string plaintext = "Hello World";

  auto ciphertext = (*recipient_context)->Seal(plaintext, associated_data_response_);
  ASSERT_TRUE(ciphertext.ok());
  EXPECT_THAT(plaintext, StrNe(*ciphertext));
}

TEST_F(RecipientContextTest, RecipientResponseContextSealFailure) {
  auto recipient_context = SetupBaseRecipient(encap_public_key_, recipient_key_pair_, info_string_);
  ASSERT_TRUE(recipient_context.ok());

  std::string empty_plaintext = "";

  auto ciphertext = (*recipient_context)->Seal(empty_plaintext, associated_data_response_);
  EXPECT_FALSE(ciphertext.ok());
  EXPECT_EQ(ciphertext.status().code(), absl::StatusCode::kInvalidArgument);
}

TEST_F(RecipientContextTest, GenerateKeysAndSetupBaseRecipientSuccess) {
  auto key_pair = KeyPair::Generate();
  ASSERT_TRUE(key_pair.ok());

  auto sender_context = SetupBaseSender(key_pair->public_key, info_string_);
  ASSERT_TRUE(sender_context.ok());

  std::string encap_public_key = (*sender_context)->GetSerializedEncapsulatedPublicKey();

  auto recipient_context = SetupBaseRecipient(encap_public_key, *key_pair, info_string_);
  EXPECT_TRUE(recipient_context.ok());
}

}  // namespace
}  // namespace oak::crypto

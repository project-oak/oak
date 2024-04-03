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

#include "cc/crypto/hpke/sender_context.h"

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "cc/crypto/hpke/utils.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::crypto {
namespace {

using ::testing::StrNe;

class SenderContextTest : public testing::Test {
 protected:
  void SetUp() override {
    std::vector<uint8_t> public_key_bytes = {
        11,  107, 5,   176, 4,   145, 171, 193, 163, 81,  105,
        238, 171, 115, 56,  160, 130, 85,  22,  227, 118, 76,
        77,  89,  144, 223, 10,  112, 11,  149, 205, 199};
    std::string serialized_public_key(public_key_bytes.begin(),
                                      public_key_bytes.end());
    serialized_public_key_ = serialized_public_key;
    info_string_ = "Test HPKE info";
    associated_data_response_ = "Test response associated data";
    associated_data_request_ = "Test request associated data";
    default_response_key_ = {166, 107, 125, 81,  22,  76,  76,  237,
                             160, 40,  232, 236, 244, 165, 13,  38,
                             157, 220, 162, 233, 235, 158, 226, 157,
                             152, 52,  162, 106, 93,  68,  12,  171};
    default_nonce_bytes_ = {1, 242, 45, 144, 96, 26, 190, 43, 156, 154, 2, 69};
  }

  SenderContext CreateTestSenderContext(
      std::unique_ptr<EVP_AEAD_CTX> response_aead_context) {
    return SenderContext(
        std::vector<uint8_t>(),
        nullptr,  // Sender request sealing is not tested in this test.
        std::move(response_aead_context));
  }

  std::string serialized_public_key_;
  std::string info_string_;
  std::string associated_data_response_;
  std::string associated_data_request_;
  std::vector<uint8_t> default_response_key_;
  std::vector<uint8_t> default_nonce_bytes_;
};

TEST_F(SenderContextTest, SetupBaseSenderReturnsUniqueEncapsulatedKey) {
  absl::StatusOr<std::unique_ptr<SenderContext>> sender_context =
      SetupBaseSender(serialized_public_key_, info_string_);
  ASSERT_TRUE(sender_context.ok());
  std::string encapsulated_public_key1 =
      (*sender_context)->GetSerializedEncapsulatedPublicKey();
  auto sender_context2 = SetupBaseSender(serialized_public_key_, info_string_);
  ASSERT_TRUE(sender_context2.ok());
  std::string encapsulated_public_key2 =
      (*sender_context2)->GetSerializedEncapsulatedPublicKey();
  EXPECT_THAT(encapsulated_public_key1, StrNe(encapsulated_public_key2));
}

TEST_F(SenderContextTest,
       SetupBaseSenderReturnsInvalidArgumentErrorForEmptyKey) {
  std::string empty_public_key = "";
  absl::StatusOr<std::unique_ptr<SenderContext>> sender_context =
      SetupBaseSender(empty_public_key, info_string_);
  EXPECT_FALSE(sender_context.ok());
  EXPECT_EQ(sender_context.status().code(), absl::StatusCode::kInvalidArgument);
}

TEST_F(SenderContextTest, SenderSealsMessageSuccess) {
  absl::StatusOr<std::unique_ptr<SenderContext>> sender_context =
      SetupBaseSender(serialized_public_key_, info_string_);
  ASSERT_TRUE(sender_context.ok());

  std::string plaintext = "Hello World";

  absl::StatusOr<const std::vector<uint8_t>> nonce = GenerateRandomNonce();
  ASSERT_TRUE(nonce.ok());
  absl::StatusOr<std::string> encrypted_request =
      (*sender_context)->Seal(*nonce, plaintext, associated_data_request_);
  EXPECT_TRUE(encrypted_request.ok());
  EXPECT_THAT(*encrypted_request, StrNe(plaintext));
}

TEST_F(SenderContextTest, SenderOpensEncryptedMessageSuccess) {
  std::vector<uint8_t> associated_data_bytes(associated_data_response_.begin(),
                                             associated_data_response_.end());

  // AEAD that Oak uses.
  const EVP_AEAD* aead_version = EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm());
  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_receive(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  // Configure sender context.
  SenderContext sender_context =
      CreateTestSenderContext(std::move(response_aead_context_receive));

  // Generate encrypted message.
  std::string plaintext_message = "Hello World";
  std::vector<uint8_t> plaintext_bytes(plaintext_message.begin(),
                                       plaintext_message.end());

  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_send(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  std::vector<uint8_t> ciphertext_bytes(plaintext_bytes.size() +
                                        EVP_HPKE_MAX_OVERHEAD);
  size_t ciphertext_size;
  ASSERT_TRUE(EVP_AEAD_CTX_seal(
      /* ctx= */ response_aead_context_send.get(),
      /* out= */ ciphertext_bytes.data(),
      /* out_len= */ &ciphertext_size,
      /* max_out_len= */ ciphertext_bytes.size(),
      /* nonce= */ default_nonce_bytes_.data(),
      /* nonce_len= */ default_nonce_bytes_.size(),
      /* in= */ plaintext_bytes.data(),
      /* in_len= */ plaintext_bytes.size(),
      /* ad= */ associated_data_bytes.data(),
      /* ad_len= */ associated_data_bytes.size()));
  ciphertext_bytes.resize(ciphertext_size);
  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());

  // Successfully open encrypted message and get back original plaintext.
  auto decyphered_message = sender_context.Open(
      default_nonce_bytes_, ciphertext, associated_data_response_);
  EXPECT_TRUE(decyphered_message.ok());

  // Cleanup the lingering context.
  EVP_AEAD_CTX_free(response_aead_context_send.release());
}

TEST_F(SenderContextTest, SenderOpensEncryptedMessageFailureNoncesNotAligned) {
  // The second set of nonce bytes are not the same.
  std::vector<uint8_t> nonce_bytes_diff = {0,   242, 45,  144, 96, 26,
                                           190, 43,  156, 154, 2,  69};

  std::vector<uint8_t> associated_data_bytes(associated_data_response_.begin(),
                                             associated_data_response_.end());

  // AEAD that Oak uses.
  const EVP_AEAD* aead_version = EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm());
  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_receive(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  // Configure sender context.
  SenderContext sender_context =
      CreateTestSenderContext(std::move(response_aead_context_receive));

  // Generate encrypted message.
  std::string plaintext_message = "Hello World";
  std::vector<uint8_t> plaintext_bytes(plaintext_message.begin(),
                                       plaintext_message.end());

  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_send(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  std::vector<uint8_t> ciphertext_bytes(plaintext_bytes.size() +
                                        EVP_HPKE_MAX_OVERHEAD);
  size_t ciphertext_size;
  ASSERT_TRUE(EVP_AEAD_CTX_seal(
      /* ctx= */ response_aead_context_send.get(),
      /* out= */ ciphertext_bytes.data(),
      /* out_len= */ &ciphertext_size,
      /* max_out_len= */ ciphertext_bytes.size(),
      /* nonce= */ nonce_bytes_diff.data(),
      /* nonce_len= */ nonce_bytes_diff.size(),
      /* in= */ plaintext_bytes.data(),
      /* in_len= */ plaintext_bytes.size(),
      /* ad= */ associated_data_bytes.data(),
      /* ad_len= */ associated_data_bytes.size()));
  ciphertext_bytes.resize(ciphertext_size);
  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());

  // Attempt to open the encrypted message. This should fail.
  auto decyphered_message = sender_context.Open(
      default_nonce_bytes_, ciphertext, associated_data_response_);
  EXPECT_FALSE(decyphered_message.ok());
  EXPECT_EQ(decyphered_message.status().code(), absl::StatusCode::kAborted);

  // Cleanup the lingering context.
  EVP_AEAD_CTX_free(response_aead_context_send.release());
}

TEST_F(SenderContextTest,
       SenderOpensEncryptedMessageFailureAssociatedDataNotAligned) {
  std::vector<uint8_t> associated_data_bytes(associated_data_response_.begin(),
                                             associated_data_response_.end());

  // AEAD that Oak uses.
  const EVP_AEAD* aead_version = EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm());
  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_receive(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  // Configure sender context.
  SenderContext sender_context =
      CreateTestSenderContext(std::move(response_aead_context_receive));

  // Generate encrypted message.
  std::string plaintext_message = "Hello World";
  std::vector<uint8_t> plaintext_bytes(plaintext_message.begin(),
                                       plaintext_message.end());

  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_send(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  std::vector<uint8_t> ciphertext_bytes(plaintext_bytes.size() +
                                        EVP_HPKE_MAX_OVERHEAD);
  size_t ciphertext_size;
  ASSERT_TRUE(EVP_AEAD_CTX_seal(
      /* ctx= */ response_aead_context_send.get(),
      /* out= */ ciphertext_bytes.data(),
      /* out_len= */ &ciphertext_size,
      /* max_out_len= */ ciphertext_bytes.size(),
      /* nonce= */ default_nonce_bytes_.data(),
      /* nonce_len= */ default_nonce_bytes_.size(),
      /* in= */ plaintext_bytes.data(),
      /* in_len= */ plaintext_bytes.size(),
      /* ad= */ associated_data_bytes.data(),
      /* ad_len= */ associated_data_bytes.size()));
  ciphertext_bytes.resize(ciphertext_size);
  std::string ciphertext(ciphertext_bytes.begin(), ciphertext_bytes.end());

  // Attempt to open the encrypted message using different associated data. This
  // should fail.
  std::string different_associated_data = "Different response associated data";
  auto decyphered_message = sender_context.Open(
      default_nonce_bytes_, ciphertext, different_associated_data);
  EXPECT_FALSE(decyphered_message.ok());
  EXPECT_EQ(decyphered_message.status().code(), absl::StatusCode::kAborted);

  // Cleanup the lingering context.
  EVP_AEAD_CTX_free(response_aead_context_send.release());
}

TEST_F(SenderContextTest, SenderOpensEmptyEncryptedMessageFailure) {
  std::vector<uint8_t> associated_data_bytes(associated_data_response_.begin(),
                                             associated_data_response_.end());

  // AEAD that Oak uses.
  const EVP_AEAD* aead_version = EVP_HPKE_AEAD_aead(EVP_hpke_aes_256_gcm());
  std::unique_ptr<EVP_AEAD_CTX> response_aead_context_receive(EVP_AEAD_CTX_new(
      /* aead= */ aead_version,
      /* key= */ default_response_key_.data(),
      /* key_len= */ default_response_key_.size(),
      /* tag_len= */ 0));

  // Configure sender context.
  SenderContext sender_context =
      CreateTestSenderContext(std::move(response_aead_context_receive));

  // We use an empty ciphertext.
  std::string ciphertext = "";
  auto decyphered_message = sender_context.Open(
      default_nonce_bytes_, ciphertext, associated_data_response_);
  EXPECT_FALSE(decyphered_message.ok());
  EXPECT_EQ(decyphered_message.status().code(),
            absl::StatusCode::kInvalidArgument);
}

}  // namespace
}  // namespace oak::crypto

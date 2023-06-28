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

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/client_encryptor.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/server_encryptor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::crypto {
namespace {

using ::testing::StrEq;

constexpr absl::string_view kOakHPKEInfoTest = "Oak Hybrid Public Key Encryption Test";
// Client Encryptor and Server Encryptor can communicate.
TEST(EncryptorTest, ClientEncryptorAndServerEncryptorCommunicateSuccess) {
  // Set up client and server encryptors.
  auto key_pair = KeyPair::Generate();
  std::string public_key = key_pair->public_key;
  auto client_encryptor = ClientEncryptor::Create(public_key);
  ASSERT_TRUE(client_encryptor.ok());
  ServerEncryptor server_encryptor = ServerEncryptor(*key_pair);

  std::string client_plaintext_message = "Hello server";

  // Encrypt plaintext message and have server encryptor decrypt message.
  auto client_ciphertext = (*client_encryptor)->Encrypt(client_plaintext_message, kOakHPKEInfoTest);
  ASSERT_TRUE(client_ciphertext.ok());
  auto server_decryption_result = server_encryptor.Decrypt(*client_ciphertext);
  ASSERT_TRUE(server_decryption_result.ok());
  EXPECT_THAT(client_plaintext_message, StrEq(server_decryption_result->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest, StrEq(server_decryption_result->associated_data));

  std::string server_plaintext_message = "Hello client";

  // Server responds with an encrypted message that the client successfully decrypts.
  auto server_ciphertext = server_encryptor.Encrypt(server_plaintext_message, kOakHPKEInfoTest);
  ASSERT_TRUE(server_ciphertext.ok());
  auto client_decryption_result = (*client_encryptor)->Decrypt(*server_ciphertext);
  ASSERT_TRUE(client_decryption_result.ok());
  EXPECT_THAT(server_plaintext_message, StrEq(client_decryption_result->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest, StrEq(client_decryption_result->associated_data));
}

TEST(EncryptorTest, ClientEncryptorAndServerEncryptorCommunicateMismatchPublicKeysFailure) {
  // Set up client and server encryptors.
  auto key_pair = KeyPair::Generate();
  std::string wrong_public_key = key_pair->public_key;
  // Edit the public key that the client uses to make it incorrect.
  wrong_public_key[0] = (wrong_public_key[0] + 1) % 128;
  auto client_encryptor = ClientEncryptor::Create(wrong_public_key);
  ASSERT_TRUE(client_encryptor.ok());
  ServerEncryptor server_encryptor = ServerEncryptor(*key_pair);

  std::string client_plaintext_message = "Hello server";

  // Encrypt plaintext message and have server encryptor decrypt message. This should result in
  // failure since the public key is incorrect.
  auto client_ciphertext = (*client_encryptor)->Encrypt(client_plaintext_message, kOakHPKEInfoTest);
  ASSERT_TRUE(client_ciphertext.ok());
  auto server_decryption_result = server_encryptor.Decrypt(*client_ciphertext);
  EXPECT_FALSE(server_decryption_result.ok());
  EXPECT_EQ(server_decryption_result.status().code(), absl::StatusCode::kAborted);
  EXPECT_THAT(server_decryption_result.status().message(),
              StrEq("Failed to open encrypted message."));
}

}  // namespace
}  // namespace oak::crypto

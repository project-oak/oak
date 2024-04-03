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

#include <string>

#include "absl/strings/string_view.h"
#include "cc/crypto/client_encryptor.h"
#include "cc/crypto/encryption_key.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/server_encryptor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::crypto {
namespace {

using ::testing::StrEq;

constexpr absl::string_view kOakHPKEInfoTest =
    "Oak Hybrid Public Key Encryption Test";
// Client Encryptor and Server Encryptor can communicate.
TEST(EncryptorTest, ClientEncryptorAndServerEncryptorCommunicateSuccess) {
  // Set up client and server encryptors.
  auto encryption_key = EncryptionKeyProvider::Create();
  ASSERT_TRUE(encryption_key.ok());
  std::string public_key = encryption_key->GetSerializedPublicKey();
  auto client_encryptor = ClientEncryptor::Create(public_key);
  ASSERT_TRUE(client_encryptor.ok());
  ServerEncryptor server_encryptor = ServerEncryptor(*encryption_key);

  // Here we have the client send 2 encrypted messages to the server to ensure
  // that nonce's align for multi-message communication.
  std::string client_plaintext_message1 = "Hello server";

  // Encrypt plaintext message and have server encryptor decrypt message.
  auto client_ciphertext1 =
      (*client_encryptor)->Encrypt(client_plaintext_message1, kOakHPKEInfoTest);
  ASSERT_TRUE(client_ciphertext1.ok());
  auto server_decryption_result1 =
      server_encryptor.Decrypt(*client_ciphertext1);
  ASSERT_TRUE(server_decryption_result1.ok());
  EXPECT_THAT(client_plaintext_message1,
              StrEq(server_decryption_result1->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest,
              StrEq(server_decryption_result1->associated_data));

  std::string client_plaintext_message2 = "Hello again, server!";
  auto client_ciphertext2 =
      (*client_encryptor)->Encrypt(client_plaintext_message2, kOakHPKEInfoTest);
  ASSERT_TRUE(client_ciphertext2.ok());
  auto server_decryption_result2 =
      server_encryptor.Decrypt(*client_ciphertext2);
  ASSERT_TRUE(server_decryption_result2.ok());
  EXPECT_THAT(client_plaintext_message2,
              StrEq(server_decryption_result2->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest,
              StrEq(server_decryption_result2->associated_data));

  // We have the server send 2 encrypted messages back to the client. Again this
  // is to ensure the nonce's align for the multiple messages.
  std::string server_plaintext_message1 = "Hello client";

  // Server responds with an encrypted message that the client successfully
  // decrypts.
  auto server_ciphertext1 =
      server_encryptor.Encrypt(server_plaintext_message1, kOakHPKEInfoTest);
  ASSERT_TRUE(server_ciphertext1.ok());
  auto client_decryption_result1 =
      (*client_encryptor)->Decrypt(*server_ciphertext1);
  ASSERT_TRUE(client_decryption_result1.ok());
  EXPECT_THAT(server_plaintext_message1,
              StrEq(client_decryption_result1->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest,
              StrEq(client_decryption_result1->associated_data));

  std::string server_plaintext_message2 = "Hello again, client!";
  auto server_ciphertext2 =
      server_encryptor.Encrypt(server_plaintext_message2, kOakHPKEInfoTest);
  ASSERT_TRUE(server_ciphertext2.ok());
  auto client_decryption_result2 =
      (*client_encryptor)->Decrypt(*server_ciphertext2);
  ASSERT_TRUE(client_decryption_result2.ok());
  EXPECT_THAT(server_plaintext_message2,
              StrEq(client_decryption_result2->plaintext));
  EXPECT_THAT(kOakHPKEInfoTest,
              StrEq(client_decryption_result2->associated_data));
}

TEST(EncryptorTest,
     ClientEncryptorAndServerEncryptorCommunicateMismatchPublicKeysFailure) {
  // Set up client and server encryptors.
  auto encryption_key = EncryptionKeyProvider::Create();
  ASSERT_TRUE(encryption_key.ok());
  std::string wrong_public_key = encryption_key->GetSerializedPublicKey();
  // Edit the public key that the client uses to make it incorrect.
  wrong_public_key[0] = (wrong_public_key[0] + 1) % 128;
  auto client_encryptor = ClientEncryptor::Create(wrong_public_key);
  ASSERT_TRUE(client_encryptor.ok());
  ServerEncryptor server_encryptor = ServerEncryptor(*encryption_key);

  std::string client_plaintext_message = "Hello server";

  // Encrypt plaintext message and have server encryptor decrypt message. This
  // should result in failure since the public key is incorrect.
  auto client_ciphertext =
      (*client_encryptor)->Encrypt(client_plaintext_message, kOakHPKEInfoTest);
  ASSERT_TRUE(client_ciphertext.ok());
  auto server_decryption_result = server_encryptor.Decrypt(*client_ciphertext);
  EXPECT_FALSE(server_decryption_result.ok());
  EXPECT_EQ(server_decryption_result.status().code(),
            absl::StatusCode::kAborted);
  EXPECT_THAT(server_decryption_result.status().message(),
              StrEq("Unable to decrypt message"));
}

}  // namespace
}  // namespace oak::crypto

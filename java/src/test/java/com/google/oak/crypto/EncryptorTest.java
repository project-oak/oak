//
// Copyright 2023 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.crypto;

import com.google.oak.crypto.DecryptionResult;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.util.Result;
import com.google.protobuf.ExtensionRegistryLite;
import java.util.Arrays;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class EncryptorTest {
  private static final byte[] TEST_REQUEST_PLAINTEXT =
      new byte[] {'R', 'e', 'q', 'u', 'e', 's', 't'};
  private static final byte[] TEST_REQUEST_ASSOCIATED_DATA = new byte[] {'d', 'a', 't', 'a', '1'};
  private static final byte[] TEST_RESPONSE_PLAINTEXT =
      new byte[] {'R', 'e', 's', 'p', 'o', 'n', 's', 'e'};
  private static final byte[] TEST_RESPONSE_ASSOCIATED_DATA = new byte[] {'d', 'a', 't', 'a', '2'};

  // Number of message exchanges done to test secure session handling.
  private static final int TEST_SESSION_SIZE = 8;

  @Test
  public void testEncryptor() throws Exception {
    // Generate key pair.
    Result<KeyPair, Exception> keyPairGenerateResult = KeyPair.generate();
    KeyPair keyPair = keyPairGenerateResult.unwrap("couldn't create key pair");

    ServerEncryptor serverEncryptor = new ServerEncryptor(keyPair);
    Result<ClientEncryptor, Exception> clientEncryptorCreateResult =
        ClientEncryptor.create(keyPair.publicKey);
    Assert.assertTrue(clientEncryptorCreateResult.isSuccess());
    ClientEncryptor clientEncryptor = clientEncryptorCreateResult.success().get();

    for (int i = 0; i < TEST_SESSION_SIZE; i++) {
      // Test request encryption/decryption.
      Result<EncryptedRequest, Exception> encryptRequestResult =
          clientEncryptor.encrypt(TEST_REQUEST_PLAINTEXT, TEST_REQUEST_ASSOCIATED_DATA);
      Assert.assertTrue(encryptRequestResult.isSuccess());
      EncryptedRequest encryptedRequest = encryptRequestResult.success().get();

      Assert.assertFalse(
          Arrays.equals(encryptedRequest.getEncryptedMessage().getCiphertext().toByteArray(),
              TEST_REQUEST_PLAINTEXT));
      Assert.assertArrayEquals(
          encryptedRequest.getEncryptedMessage().getAssociatedData().toByteArray(),
          TEST_REQUEST_ASSOCIATED_DATA);

      Result<DecryptionResult, Exception> decryptRequestResult =
          serverEncryptor.decrypt(encryptedRequest);
      Assert.assertTrue(decryptRequestResult.isSuccess());
      Assert.assertArrayEquals(
          decryptRequestResult.success().get().plaintext, TEST_REQUEST_PLAINTEXT);
      Assert.assertArrayEquals(
          decryptRequestResult.success().get().associatedData, TEST_REQUEST_ASSOCIATED_DATA);

      // Test response encryption/decryption.
      Result<EncryptedResponse, Exception> encryptResponseResult =
          serverEncryptor.encrypt(TEST_RESPONSE_PLAINTEXT, TEST_RESPONSE_ASSOCIATED_DATA);
      Assert.assertTrue(encryptResponseResult.isSuccess());
      EncryptedResponse encryptedResponse = encryptResponseResult.success().get();

      Assert.assertFalse(
          Arrays.equals(encryptedResponse.getEncryptedMessage().getCiphertext().toByteArray(),
              TEST_RESPONSE_PLAINTEXT));
      Assert.assertArrayEquals(
          encryptedResponse.getEncryptedMessage().getAssociatedData().toByteArray(),
          TEST_RESPONSE_ASSOCIATED_DATA);

      Result<DecryptionResult, Exception> decryptResponseResult =
          clientEncryptor.decrypt(encryptedResponse);
      Assert.assertTrue(decryptResponseResult.isSuccess());
      Assert.assertArrayEquals(
          decryptResponseResult.success().get().plaintext, TEST_RESPONSE_PLAINTEXT);
      Assert.assertArrayEquals(
          decryptResponseResult.success().get().associatedData, TEST_RESPONSE_ASSOCIATED_DATA);
    }
    serverEncryptor.close();
    clientEncryptor.close();
  }
}

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

import com.google.oak.crypto.ClientEncryptor;
import com.google.oak.util.Result;
import java.nio.charset.StandardCharsets;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class ClientEncryptorTest {
  private static final byte[] TEST_SERIALIZED_SERVER_PUBLIC_KEY = new byte[0];
  private static final byte[] TEST_PLAINTEXT = new byte[0];
  private static final byte[] TEST_ASSOCIATED_DATA = new byte[0];
  private static final byte[] TEST_ENCRYPTED_MESSAGE = new byte[0];

  @Test
  public void testEncryptDecrypt() throws Exception {
    // TODO(#3644): Implement and test Java hybrid encryption.
    ClientEncryptor encryptor = new ClientEncryptor(TEST_SERIALIZED_SERVER_PUBLIC_KEY);

    Result<byte[], Exception> encrypt_result =
        encryptor.encrypt(TEST_PLAINTEXT, TEST_ASSOCIATED_DATA);
    Assert.assertTrue(encrypt_result.isSuccess());
    Assert.assertArrayEquals(encrypt_result.success().get(), TEST_ENCRYPTED_MESSAGE);

    Result<ClientEncryptor.DecryptionResult, Exception> decrypt_result =
        encryptor.decrypt(TEST_ENCRYPTED_MESSAGE);
    Assert.assertTrue(decrypt_result.isSuccess());
    Assert.assertArrayEquals(decrypt_result.success().get().plaintext, TEST_PLAINTEXT);
    Assert.assertArrayEquals(decrypt_result.success().get().associatedData, TEST_ASSOCIATED_DATA);
  }
}

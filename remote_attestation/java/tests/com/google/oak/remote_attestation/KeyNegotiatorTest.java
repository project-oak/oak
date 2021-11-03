//
// Copyright 2021 The Project Oak Authors
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

package com.google.oak.remote_attestation;

import com.google.oak.remote_attestation.AeadEncryptor;
import com.google.oak.remote_attestation.KeyNegotiator;
import com.google.oak.remote_attestation.Message;
import java.io.IOException;
import java.security.GeneralSecurityException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class KeyNegotiatorTest {
  private static final byte[] DATA = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

  private KeyNegotiator clientKeyNegotiator;
  private KeyNegotiator serverKeyNegotiator;

  @Before
  public void setUp() {
    clientKeyNegotiator = new KeyNegotiator();
    serverKeyNegotiator = new KeyNegotiator();
  }

  @Test
  public void testCreateKeyNegotiator() throws GeneralSecurityException {
    byte[] publicKey = clientKeyNegotiator.getPublicKey();
    Assert.assertEquals(Message.EPHEMERAL_PUBLIC_KEY_LENGTH, publicKey.length);
  }

  @Test
  public void testCreateEncryptor() throws GeneralSecurityException, IOException {
    byte[] clientEphemeralPublicKey = clientKeyNegotiator.getPublicKey();
    byte[] serverEphemeralPublicKey = serverKeyNegotiator.getPublicKey();

    AeadEncryptor clientEncryptor = clientKeyNegotiator.createEncryptor(
        serverEphemeralPublicKey, KeyNegotiator.EncryptorType.CLIENT);
    AeadEncryptor serverEncryptor = serverKeyNegotiator.createEncryptor(
        clientEphemeralPublicKey, KeyNegotiator.EncryptorType.SERVER);

    byte[] encryptedClientData = clientEncryptor.encrypt(DATA);
    byte[] decryptedClientData = serverEncryptor.decrypt(encryptedClientData);
    Assert.assertArrayEquals(decryptedClientData, DATA);

    byte[] encryptedServerData = serverEncryptor.encrypt(DATA);
    byte[] decryptedServerData = clientEncryptor.decrypt(encryptedServerData);
    Assert.assertArrayEquals(decryptedServerData, DATA);
  }
}

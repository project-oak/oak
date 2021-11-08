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

import com.google.oak.remote_attestation.Message;
import java.io.IOException;
import java.util.Random;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class MessageTest {
  private static final int TEST_LENGTH = 100;

  @Test
  public void testSerializeClientHello() throws IOException {
    byte[] random = getRandomArray(Message.REPLAY_PROTECTION_ARRAY_LENGTH);

    Message.ClientHello clientHello = new Message.ClientHello(random);
    byte[] serializedClientHello = clientHello.serialize();
    Message.ClientHello deserializedClientHello =
        Message.ClientHello.deserialize(serializedClientHello);

    Assert.assertArrayEquals(clientHello.getRandom(), deserializedClientHello.getRandom());
  }

  @Test
  public void testSerializeServerIdentity() throws IOException {
    byte[] ephemeralPublicKey = getRandomArray(Message.EPHEMERAL_PUBLIC_KEY_LENGTH);
    byte[] random = getRandomArray(Message.REPLAY_PROTECTION_ARRAY_LENGTH);
    byte[] transcriptSignature = getRandomArray(Message.TRANSCRIPT_SIGNATURE_LENGTH);
    byte[] signingPublicKey = getRandomArray(Message.SIGNING_PUBLIC_KEY_LENGTH);
    byte[] attestationInfo = getRandomArray(TEST_LENGTH);
    byte[] additionalInfo = getRandomArray(TEST_LENGTH);

    Message.ServerIdentity serverIdentity = new Message.ServerIdentity(
        ephemeralPublicKey, random, signingPublicKey, attestationInfo, additionalInfo);
    serverIdentity.setTranscriptSignature(transcriptSignature);
    byte[] serializedServerIdentity = serverIdentity.serialize();
    Message.ServerIdentity deserializedServerIdentity =
        Message.ServerIdentity.deserialize(serializedServerIdentity);

    Assert.assertArrayEquals(
        serverIdentity.getEphemeralPublicKey(), deserializedServerIdentity.getEphemeralPublicKey());
    Assert.assertArrayEquals(serverIdentity.getRandom(), deserializedServerIdentity.getRandom());
    Assert.assertArrayEquals(serverIdentity.getTranscriptSignature(),
        deserializedServerIdentity.getTranscriptSignature());
    Assert.assertArrayEquals(
        serverIdentity.getSigningPublicKey(), deserializedServerIdentity.getSigningPublicKey());
    Assert.assertArrayEquals(
        serverIdentity.getAttestationInfo(), deserializedServerIdentity.getAttestationInfo());
  }

  @Test
  public void testSerializeClientIdentity() throws IOException {
    byte[] ephemeralPublicKey = getRandomArray(Message.EPHEMERAL_PUBLIC_KEY_LENGTH);
    byte[] transcriptSignature = getRandomArray(Message.TRANSCRIPT_SIGNATURE_LENGTH);
    byte[] signingPublicKey = getRandomArray(Message.SIGNING_PUBLIC_KEY_LENGTH);
    byte[] attestationInfo = getRandomArray(TEST_LENGTH);

    Message.ClientIdentity clientIdentity =
        new Message.ClientIdentity(ephemeralPublicKey, signingPublicKey, attestationInfo);
    clientIdentity.setTranscriptSignature(transcriptSignature);
    byte[] serializedClientIdentity = clientIdentity.serialize();
    Message.ClientIdentity deserializedClientIdentity =
        Message.ClientIdentity.deserialize(serializedClientIdentity);

    Assert.assertArrayEquals(
        clientIdentity.getEphemeralPublicKey(), deserializedClientIdentity.getEphemeralPublicKey());
    Assert.assertArrayEquals(clientIdentity.getTranscriptSignature(),
        deserializedClientIdentity.getTranscriptSignature());
    Assert.assertArrayEquals(
        clientIdentity.getSigningPublicKey(), deserializedClientIdentity.getSigningPublicKey());
    Assert.assertArrayEquals(
        clientIdentity.getAttestationInfo(), deserializedClientIdentity.getAttestationInfo());
  }

  @Test
  public void testSerializeEncryptedData() throws IOException {
    byte[] nonce = getRandomArray(Message.NONCE_LENGTH);
    byte[] data = getRandomArray(TEST_LENGTH);

    Message.EncryptedData encryptedData = new Message.EncryptedData(nonce, data);
    byte[] serializedEncryptedData = encryptedData.serialize();
    Message.EncryptedData deserializedEncryptedData =
        Message.EncryptedData.deserialize(serializedEncryptedData);

    Assert.assertArrayEquals(encryptedData.getNonce(), deserializedEncryptedData.getNonce());
    Assert.assertArrayEquals(encryptedData.getData(), deserializedEncryptedData.getData());
  }

  private byte[] getRandomArray(int length) {
    byte[] random = new byte[length];
    new Random().nextBytes(random);
    return random;
  }
}

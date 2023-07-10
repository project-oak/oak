//
// Copyright 2022 The Project Oak Authors
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

package com.google.oak.client;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.google.oak.crypto.ClientEncryptor;
import com.google.oak.crypto.Encryptor;
import com.google.oak.crypto.ServerEncryptor;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.v1.AeadEncryptedMessage;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.remote_attestation.InsecureAttestationVerifier;
import com.google.oak.session.v1.AttestationBundle;
import com.google.oak.session.v1.AttestationEndorsement;
import com.google.oak.session.v1.AttestationEvidence;
import com.google.oak.transport.EvidenceProvider;
import com.google.oak.transport.Transport;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Optional;
import org.junit.Test;

public class OakClientTest {
  private static final byte[] TEST_REQUEST = new byte[] {'R', 'e', 'q', 'u', 'e', 's', 't'};
  private static final byte[] TEST_RESPONSE = new byte[] {'R', 'e', 's', 'p', 'o', 'n', 's', 'e'};
  private static final byte[] TEST_ASSOCIATED_DATA = new byte[0];

  // Number of message exchanges done to test secure session handling.
  private static final int TEST_SESSION_SIZE = 8;

  private static class TestTransport implements EvidenceProvider, Transport {
    private final KeyPair keyPair;
    private final ServerEncryptor serverEncryptor;

    public TestTransport() {
      this.keyPair = KeyPair.generate().unwrap("couldn't create key pair");
      this.serverEncryptor = new ServerEncryptor(keyPair);
    }

    @Override
    public Result<AttestationBundle, String> getEvidence() {
      AttestationEvidence attestationEvidence =
          AttestationEvidence.newBuilder()
              .setEncryptionPublicKey(ByteString.copyFrom(keyPair.publicKey))
              .build();
      AttestationEndorsement attestationEndorsement = AttestationEndorsement.getDefaultInstance();
      AttestationBundle attestationBundle = AttestationBundle.newBuilder()
                                                .setAttestationEvidence(attestationEvidence)
                                                .setAttestationEndorsement(attestationEndorsement)
                                                .build();

      return Result.success(attestationBundle);
    }

    @Override
    public Result<byte[], String> invoke(byte[] requestBytes) {
      // Result<Encryptor.DecryptionResult, Exception> decryptRequestResult =
      //     serverEncryptor.decrypt(requestBytes);
      // if (decryptRequestResult.isError()) {
      //   return Result.error("couldn't decrypt request");
      // }
      // Encryptor.DecryptionResult decryptedRequest = decryptRequestResult.success().get();
      // if (!Arrays.equals(decryptedRequest.plaintext, TEST_REQUEST)
      //     || !Arrays.equals(decryptedRequest.associatedData, TEST_ASSOCIATED_DATA)) {
      //   return Result.error("incorrect request");
      // }

      // Result<byte[], Exception> encryptResponseResult =
      //     serverEncryptor.encrypt(TEST_RESPONSE, TEST_ASSOCIATED_DATA);
      // if (encryptResponseResult.isError()) {
      //   return Result.error("couldn't encrypt response");
      // }
      // byte[] serializedEncryptedResponse = encryptResponseResult.success().get();

      // return Result.success(serializedEncryptedResponse);





      Result<Encryptor.DecryptionResult, Exception> decryptRequestResult =
          serverEncryptor.decrypt(requestBytes);

      return decryptRequestResult
          .mapError(err -> Result.error("couldn't decrypt request: " + err))
          .map(decryptedRequest -> {
            if (!Arrays.equals(decryptedRequest.plaintext, TEST_REQUEST)
                || !Arrays.equals(decryptedRequest.associatedData, TEST_ASSOCIATED_DATA)) {
              return Result.error("incorrect request");
            }
            Result<byte[], Exception> encryptResponseResult = serverEncryptor
                .encrypt(TEST_RESPONSE, TEST_ASSOCIATED_DATA);
            return encryptResponseResult
              .mapError(err -> Result.error("couldn't encrypt response: " + err));
          });
    }

    @Override
    public void close() throws Exception {
      // No resources to close.
    }
  }

  /** This test demonstrates the use of the {@code com.google.oak.client.OakClient} API. */
  @Test
  public void testOakClient() throws Exception {
    Result<OakClient<TestTransport>, Exception> oakClientCreateResult =
        OakClient.create(new TestTransport(), new InsecureAttestationVerifier());
    assertTrue(oakClientCreateResult.isSuccess());

    try (OakClient<TestTransport> oakClient = oakClientCreateResult.success().get()) {
      for (int i = 0; i < TEST_SESSION_SIZE; i++) {
        Result<byte[], Exception> oakClientInvokeResult = oakClient.invoke(TEST_REQUEST);
        assertTrue(oakClientInvokeResult.isSuccess());
        System.out.print(oakClientInvokeResult.success().get().length);
        assertArrayEquals(oakClientInvokeResult.success().get(), TEST_RESPONSE);
      }
    }
  }
}

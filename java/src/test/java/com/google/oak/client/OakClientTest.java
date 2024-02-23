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
import static org.junit.Assert.assertTrue;

import com.google.oak.attestation.v1.AttestationResults;
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.crypto.ServerEncryptor;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.remote_attestation.AttestationVerifier;
import com.google.oak.session.v1.EndorsedEvidence;
import com.google.oak.transport.EvidenceProvider;
import com.google.oak.transport.Transport;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import java.time.Clock;
import java.time.Instant;
import java.util.Arrays;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class OakClientTest {
  private static final byte[] TEST_REQUEST = new byte[] {'R', 'e', 'q', 'u', 'e', 's', 't'};
  private static final byte[] TEST_RESPONSE = new byte[] {'R', 'e', 's', 'p', 'o', 'n', 's', 'e'};
  private static final byte[] TEST_ASSOCIATED_DATA = new byte[0];

  private final KeyPair keyPair = KeyPair.generate().unwrap("couldn't create key pair");

  // Number of message exchanges done to test secure session handling.
  // TODO(#4157): Support crypto sessions on the server and increase the test
  // session size to 8.
  private static final int TEST_SESSION_SIZE = 1;

  public static class TestAttestationVerifier implements AttestationVerifier {
    private final AttestationResults attestationResults;

    public TestAttestationVerifier(AttestationResults attestationResults) {
      this.attestationResults = attestationResults;
    }

    @Override
    public final Result<AttestationResults, Exception> verify(
        Instant now, final Evidence evidence, final Endorsements endorsements) {
      return Result.success(attestationResults);
    }
  }

  private static class TestTransport implements EvidenceProvider, Transport {
    private final ServerEncryptor serverEncryptor;

    public TestTransport(KeyPair keyPair) {
      this.serverEncryptor = new ServerEncryptor(keyPair);
    }

    @Override
    public Result<EndorsedEvidence, String> getEndorsedEvidence() {
      Evidence evidence = Evidence.getDefaultInstance();
      Endorsements endorsements = Endorsements.getDefaultInstance();
      EndorsedEvidence endorsedEvidence =
          EndorsedEvidence.newBuilder().setEvidence(evidence).setEndorsements(endorsements).build();

      return Result.success(endorsedEvidence);
    }

    @Override
    public Result<EncryptedResponse, String> invoke(EncryptedRequest encryptedRequest) {
      return serverEncryptor.decrypt(encryptedRequest)
          .mapError(err -> "couldn't decrypt request: " + err)
          .andThen(decryptedRequest -> {
            if (!Arrays.equals(decryptedRequest.plaintext, TEST_REQUEST)
                || !Arrays.equals(decryptedRequest.associatedData, TEST_ASSOCIATED_DATA)) {
              return Result.error("incorrect request");
            }
            return serverEncryptor.encrypt(TEST_RESPONSE, TEST_ASSOCIATED_DATA)
                .mapError(err -> "couldn't encrypt response: " + err);
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
    AttestationResults attestationResults =
        AttestationResults.newBuilder()
            .setEncryptionPublicKey(ByteString.copyFrom(keyPair.publicKey))
            .build();
    Result<OakClient<TestTransport>, Exception> oakClientCreateResult =
        OakClient.create(new TestTransport(keyPair),
            new TestAttestationVerifier(attestationResults), Clock.systemUTC());
    assertTrue(oakClientCreateResult.isSuccess());

    try (OakClient<TestTransport> oakClient = oakClientCreateResult.success().get()) {
      for (int i = 0; i < TEST_SESSION_SIZE; i++) {
        Result<byte[], Exception> oakClientInvokeResult = oakClient.invoke(TEST_REQUEST);
        assertTrue(oakClientInvokeResult.isSuccess());
        assertArrayEquals(oakClientInvokeResult.success().get(), TEST_RESPONSE);
      }
    }
  }
}

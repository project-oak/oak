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
import java.util.Optional;
import org.junit.Test;

public class OakClientTest {
  private static final byte[] TEST_SERVER_ENCRYPTION_PUBLIC_KEY = new byte[0];
  private static final byte[] TEST_REQUEST = new byte[] {'R', 'e', 'q', 'u', 'e', 's', 't'};
  private static final byte[] TEST_RESPONSE = new byte[] {'R', 'e', 's', 'p', 'o', 'n', 's', 'e'};
  private static final byte[] TEST_ASSOCIATED_DATA = new byte[0];

  private static class TestTransport implements EvidenceProvider, Transport {
    @Override
    public Result<AttestationBundle, String> getEvidence() {
      // TODO(#3642): Use hybrid encryption and return server encryption public key.
      AttestationEvidence attestationEvidence =
          AttestationEvidence.newBuilder()
              .setEncryptionPublicKey(ByteString.copyFrom(TEST_SERVER_ENCRYPTION_PUBLIC_KEY))
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
      // TODO(#3642): Use hybrid encryption for requests and responses.
      EncryptedResponse encryptedResponse =
          EncryptedResponse.newBuilder()
              .setEncryptedMessage(AeadEncryptedMessage.newBuilder()
                                       .setCiphertext(ByteString.copyFrom(TEST_RESPONSE))
                                       .setAssociatedData(ByteString.copyFrom(TEST_ASSOCIATED_DATA))
                                       .build())
              .build();
      return Result.success(encryptedResponse.toByteArray());
    }

    @Override
    public void close() throws Exception {
      // No resources to close.
    }
  }

  /** This test demonstrates the use of the {@code com.google.oak.client.OakClient} API. */
  @Test
  public void testOakClient() {
    Result<OakClient<TestTransport>, Exception> oakClientCreateResult =
        OakClient.create(new TestTransport(), new InsecureAttestationVerifier());
    assertTrue(oakClientCreateResult.isSuccess());
    OakClient<TestTransport> oakClient = oakClientCreateResult.success().get();

    Result<byte[], Exception> oakClientInvokeResult = oakClient.invoke(TEST_REQUEST);
    assertTrue(oakClientInvokeResult.isSuccess());
    assertArrayEquals(oakClientInvokeResult.success().get(), TEST_RESPONSE);
  }
}

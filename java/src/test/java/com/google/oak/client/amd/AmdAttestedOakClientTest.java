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

package com.google.oak.client.amd;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;

import com.google.common.hash.Hashing;
import com.google.oak.client.Encryptor;
import com.google.oak.client.RpcClient;
import com.google.oak.evidence.AmdAttestationReport;
import com.google.oak.evidence.BasicEvidence;
import com.google.oak.evidence.EndorsementEvidence;
import com.google.oak.evidence.Evidence;
import com.google.oak.util.Result;
import java.util.Optional;
import org.junit.Before;
import org.junit.Test;
import org.mockito.AdditionalMatchers;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.Mockito;

public class AmdAttestedOakClientTest {
  private RpcClient rpcClient = Mockito.mock(RpcClient.class);
  private Encryptor encryptor = Mockito.mock(Encryptor.class);
  static final byte[] MESSAGE_BYTES = new byte[] {'H', 'e', 'l', 'l', 'o'};
  static final byte[] ENCRYPTED_BYTES = new byte[] {'1', '2', '3', '4', '5'};

  @Before
  public void setup() {
    when(rpcClient.send(any(byte[].class))).thenReturn(Result.success(MESSAGE_BYTES));
    when(encryptor.encrypt(any(byte[].class))).thenReturn(Result.success(ENCRYPTED_BYTES));
    when(encryptor.decrypt(any(byte[].class))).thenReturn(Result.success(MESSAGE_BYTES));
  }

  @Test
  public void testSend() {
    AmdAttestedOakClient<RpcClient> oakClient =
        new AmdAttestedOakClient.Builder<>()
            .withEvidenceProvider(() -> evidenceForTest())
            .withEncryptorProvider(publicKey -> Result.success(encryptor))
            .withClientProvider(() -> Result.success(rpcClient))
            .build()
            .success()
            .get();
    Result<byte[], Exception> response = oakClient.send(MESSAGE_BYTES);
    assertTrue(response.isSuccess());
    assertEquals(MESSAGE_BYTES, response.success().get());
  }

  Result<BasicEvidence<AmdAttestationReport>, Exception> evidenceForTest() {
    byte[] testPublicKey = new byte[] {0, 1, 2};
    byte[] testPublicKeyHash = Hashing.sha256().hashBytes(testPublicKey).asBytes();
    BasicEvidence<AmdAttestationReport> evidence = new BasicEvidence<>(
        AmdAttestationReport.createPlaceholder(testPublicKeyHash, new byte[] {}),
        new EndorsementEvidence(), testPublicKey);
    return Result.success(evidence);
  }
}

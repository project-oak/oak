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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.google.oak.util.Result;
import java.nio.charset.StandardCharsets;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.Test;

public class OakClientTest {
  /**
   * This test demonstrates the use of the API provided by the classes and interfaces in {@code
   * com.google.oak.client}.
   */
  @Test
  public void testSend() {
    PilotAttestationClient attestationClient = new PilotAttestationClient();
    PilotOakClient oakClient = new PilotOakClient.Builder(attestationClient).build();
    Result<String, Exception> response = oakClient.send("Hello!");
    assertTrue(response.isSuccess());
    assertEquals("Hello!", response.success().get());
  }

  private static class PilotOakClient extends OakClient<String, String> {
    final PilotRpcClient rpcClient;
    final Encryptor encryptor;

    PilotOakClient(final Builder builder) {
      byte[] signingPublicKey = builder.attestationClient.verifyEvidence(new Evidence() {});
      // In reality implementations of OakClient must handle empty Optionals and unexpected types.
      rpcClient = (PilotRpcClient) builder.rpcClientProvider.getRpcClient().success().get();
      encryptor = builder.encryptorProvider.getEncryptor(signingPublicKey).success().get();
    }

    @Override
    public void close() throws Exception {
      rpcClient.close();
    }

    @Override
    Result<String, Exception> send(final String request) {
      return encryptor.encrypt(request.getBytes())
          .andThen(rpcClient::send)
          .andThen(encryptor::decrypt)
          .map(b -> new String(b, StandardCharsets.UTF_8));
    }

    static class Builder extends OakClient.Builder<String, String, Builder> {
      final PilotAttestationClient attestationClient;

      Builder(final PilotAttestationClient attestationClient) {
        super(attestationClient, attestationClient);
        this.attestationClient = attestationClient;
      }

      @Override
      PilotOakClient build() {
        return new PilotOakClient(this);
      }

      @Override
      protected Builder self() {
        return this;
      }
    }
  }

  private static class PilotAttestationClient
      implements OakClient.EncryptorProvider, OakClient.RpcClientProvider {
    final PilotRpcClient rpcClient;
    final Encryptor encryptor = new Encryptor() {
      @Override
      public Result<byte[], Exception> encrypt(final byte[] data) {
        return Result.success(data);
      }

      @Override
      public Result<byte[], Exception> decrypt(final byte[] data) {
        return Result.success(data);
      }
    };

    PilotAttestationClient() {
      this.rpcClient = new PilotRpcClient();
    }

    // This function will eventually be provided by an EvidenceProvider.
    byte[] verifyEvidence(Evidence evidence) {
      return "TestSigningPublicKey".getBytes(StandardCharsets.UTF_8);
    }

    @Override
    public Result<? extends RpcClient, Exception> getRpcClient() {
      return Result.success(rpcClient);
    }

    @Override
    public Result<? extends Encryptor, Exception> getEncryptor(byte[] unusedSigningPublicKey) {
      if (unusedSigningPublicKey.length > 0) {
        return Result.success(encryptor);
      }
      return Result.error(new IllegalArgumentException("public key cannot be empty"));
    }
  }

  private static class PilotRpcClient implements RpcClient {
    @Override
    public void close() throws Exception {
      // No resources to close
    }

    @Override
    public Result<byte[], Exception> send(final byte[] request) {
      return Result.success(request);
    }
  }
}

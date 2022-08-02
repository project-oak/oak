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

import static com.google.oak.remote_attestation.KeyNegotiator.EncryptorType.CLIENT;

import com.google.oak.client.AeadEncryptor;
import com.google.oak.client.Encryptor;
import com.google.oak.client.OakClient;
import com.google.oak.client.RpcClient;
import com.google.oak.evidence.AmdAttestationReport;
import com.google.oak.evidence.BasicEvidence;
import com.google.oak.evidence.EndorsementEvidence;
import com.google.oak.remote_attestation.KeyNegotiator;
import com.google.oak.util.Result;
import java.security.GeneralSecurityException;

/**
 * Placeholder implementation of an AmdAttestedOakClient. To create an instance of this class, an
 * {@code AmdAttestationReport} must be received and verified.
 *
 * This implementation uses {@code byte[]} as the type of the request and response.
 */
public class AmdAttestedOakClient<C extends RpcClient> implements OakClient<byte[], byte[]> {
  private final C client;
  private final Encryptor encryptor;

  private AmdAttestedOakClient(final Encryptor encryptor, final C client) {
    this.client = client;
    this.encryptor = encryptor;
  }

  @Override
  public Result<byte[], Exception> send(byte[] request) {
    return encryptor.encrypt(request)
        .andThen(bytes -> client.send(bytes))
        .andThen(response -> encryptor.decrypt(response));
  }

  @Override
  public void close() throws Exception {
    client.close();
  }

  /**
   * Builder for {@code AttestedClient}.
   */
  public static class Builder<C extends RpcClient> {
    private RpcClientProvider<C> clientProvider;
    private EvidenceProvider<BasicEvidence<AmdAttestationReport>> evidenceProvider =
        defaultEvidenceProvider();
    private EncryptorProvider<? extends Encryptor> encryptorProvider = defaultEncryptorProvider();

    /**
     * Configures this builder to use the given {@code RpcClientProvider}.
     *
     * @param clientProvider provides an instance of {@code <C>}
     * @return this builder
     */
    public Builder<C> withClientProvider(RpcClientProvider<C> clientProvider) {
      this.clientProvider = clientProvider;
      return this;
    }

    /**
     * Configures this builder to use the given {@code EvidenceProvider}.
     *
     * @param evidenceProvider provides an instance of {@code BasicEvidence<AmdAttestationReport>}
     * @return this builder
     */
    public Builder<C> withEvidenceProvider(
        EvidenceProvider<BasicEvidence<AmdAttestationReport>> evidenceProvider) {
      this.evidenceProvider = evidenceProvider;
      return this;
    }

    /**
     * Configures this builder to use the given {@code EncryptorProvider}.
     *
     * @param encryptorProvider provides an instance of {@code Encryptor}
     * @return this builder
     */
    public Builder<C> withEncryptorProvider(
        EncryptorProvider<? extends Encryptor> encryptorProvider) {
      this.encryptorProvider = encryptorProvider;
      return this;
    }

    /**
     * Verifies the evidence provided by {@code evidenceProvider}. If successful, feeds the
     * resulting publicKey to {@code encryptorProvider} to generate an encryptor. Returns an error
     * if any of the steps fail.
     *
     * <p>{@code clientProvider}, {@code evidenceProvider}, and {@code encryptorProvider} must all
     * be non-null.
     *
     * @return an instance of {@code AttestedClient<C>} or an error, wrapped in a {@code Result}
     */
    public Result<AmdAttestedOakClient<C>, Exception> build() {
      if (clientProvider == null || evidenceProvider == null || encryptorProvider == null) {
        return Result.error(new Exception(String.format(
            "nonnull values for clientProvider (%s), evidenceProvider (%s), and encryptorProvider (%s) must be provided",
            clientProvider, evidenceProvider, encryptorProvider)));
      }

      Result<C, Exception> clientResult = clientProvider.getRpcClient();
      Result<? extends Encryptor, Exception> encryptorResult =
          evidenceProvider.getEvidence().andThen(evidence
              -> evidence.verify().andThen(publicKey -> encryptorProvider.getEncryptor(publicKey)));

      return Result.merge(encryptorResult, clientResult,
          (encryptor, client) -> new AmdAttestedOakClient(encryptor, client));
    }

    /**
     * Creates and returns a simple {@code EncryptorProvider} that resembles the Encryptor from
     * offline attestation.
     */
    EncryptorProvider<Encryptor> defaultEncryptorProvider() {
      return new EncryptorProvider<Encryptor>() {
        @Override
        public Result<Encryptor, Exception> getEncryptor(byte[] signingPublicKey) {
          KeyNegotiator keyNegotiator = new KeyNegotiator();
          try {
            AeadEncryptor encryptor =
                new AeadEncryptor(keyNegotiator.createEncryptor(signingPublicKey, CLIENT));
            return Result.success(encryptor);
          } catch (GeneralSecurityException e) {
            return Result.error(e);
          }
        }
      };
    }

    // TODO(#2842): Update this to provide a more interesting default or remove.
    /**
     * Creates and returns a simple {@code EvidenceProvider} that contains an empty
     * {@code AmdAttestationReport}.
     */
    EvidenceProvider<BasicEvidence<AmdAttestationReport>> defaultEvidenceProvider() {
      return new EvidenceProvider<BasicEvidence<AmdAttestationReport>>() {
        @Override
        public Result<BasicEvidence<AmdAttestationReport>, Exception> getEvidence() {
          BasicEvidence<AmdAttestationReport> evidence = new BasicEvidence<>(
              AmdAttestationReport.createPlaceholder(new byte[] {}, new byte[] {}),
              new EndorsementEvidence());
          return Result.success(evidence);
        }
      };
    }
  }
}

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

import com.google.oak.crypto.ClientEncryptor;
import com.google.oak.crypto.Encryptor;
import com.google.oak.remote_attestation.AttestationVerifier;
import com.google.oak.transport.EvidenceProvider;
import com.google.oak.transport.Transport;
import com.google.oak.util.Result;
import oak.session.noninteractive.v1.AttestationBundle;
import oak.session.noninteractive.v1.AttestationEndorsement;
import oak.session.noninteractive.v1.AttestationEvidence;

/**
 * Oak Client class for exchanging encrypted messages with an Oak Enclave which is being run by the
 * Oak Launcher.
 *
 * @param T type of the transport used to communicate with an Oak Launcher.
 */
public class OakClient<T extends Transport> {
  private static final byte[] EMPTY_ASSOCIATED_DATA = new byte[0];

  private final T transport;
  private final byte[] serverEncryptionPublicKey;

  /**
   * Create an instance of the Oak Client by remotely attesting an Oak Enclave and creating an
   * encrypted channel.
   *
   * @param <E> type that implements interfaces for the transport and for the evidence provider.
   * @param <V> type that implements an interface for the attestation verifier.
   * @return an instance of the {@code OakClient} wrapped in a {@code Result}
   */
  public static <E extends EvidenceProvider & Transport, V extends AttestationVerifier>
      Result<OakClient<E>, Exception> create(E transport, V verifier) {
    // TODO(#3641): Implement client-side attestation verification.
    Result<AttestationBundle, String> getEvidenceResult = transport.getEvidence();
    if (getEvidenceResult.isError()) {
      return Result.error(new Exception(getEvidenceResult.error().get()));
    }
    AttestationEvidence attestationEvidence =
        getEvidenceResult.success().get().getAttestationEvidence();
    AttestationEndorsement attestationEndorsement =
        getEvidenceResult.success().get().getAttestationEndorsement();

    Result<Boolean, Exception> verifyResult =
        verifier.verify(attestationEvidence, attestationEndorsement);
    if (getEvidenceResult.isError()) {
      return Result.error(new Exception(getEvidenceResult.error().get()));
    }

    OakClient<E> oakClient =
        new OakClient<E>(transport, attestationEvidence.getEncryptionPublicKey().toByteArray());
    return Result.success(oakClient);
  }

  private OakClient(T transport, byte[] serverEncryptionPublicKey) {
    this.transport = transport;
    this.serverEncryptionPublicKey = serverEncryptionPublicKey;
  }

  /**
   * Invoke the provided method by fetching and verifying the attested enclave public key, and then
   * using it to encrypt the request body.
   *
   * @param requestBody request byte representation.
   * @return response byte representation wrapped in a {@code Result}
   */
  // TODO(#3466): Actually implement attestation and encryption.
  public Result<byte[], Exception> invoke(byte[] requestBody) {
    Result<ClientEncryptor, Exception> encryptorCreateResult =
        ClientEncryptor.create(this.serverEncryptionPublicKey);
    if (encryptorCreateResult.isError()) {
      return Result.error(new Exception(encryptorCreateResult.error().get()));
    }
    ClientEncryptor encryptor = encryptorCreateResult.success().get();

    // Encrypt request.
    Result<byte[], Exception> encryptResult = encryptor.encrypt(requestBody, EMPTY_ASSOCIATED_DATA);
    if (encryptResult.isError()) {
      return Result.error(new Exception(encryptResult.error().get()));
    }
    byte[] encryptedRequest = encryptResult.success().get();

    // Send request.
    Result<byte[], String> invokeResult = this.transport.invoke(encryptedRequest);
    if (invokeResult.isError()) {
      return Result.error(new Exception(invokeResult.error().get()));
    }
    byte[] encryptedResponse = invokeResult.success().get();

    // Decrypt response.
    Result<Encryptor.DecryptionResult, Exception> decryptResult =
        encryptor.decrypt(encryptedResponse);
    if (decryptResult.isError()) {
      return Result.error(new Exception(decryptResult.error().get()));
    }
    // Currently we ignore the associated data.
    byte[] responseBody = decryptResult.success().get().plaintext;

    return Result.success(responseBody);
  }
}

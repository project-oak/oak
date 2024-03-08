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

import com.google.oak.attestation.v1.AttestationResults;
import com.google.oak.crypto.ClientEncryptor;
import com.google.oak.remote_attestation.AttestationVerifier;
import com.google.oak.transport.EvidenceProvider;
import com.google.oak.transport.Transport;
import com.google.oak.util.Result;
import java.time.Clock;

/**
 * Oak Client class for exchanging encrypted messages with an Oak Enclave which is being run by the
 * Oak Launcher.
 */
public class OakClient<T extends Transport> implements AutoCloseable {
  private static final byte[] EMPTY_ASSOCIATED_DATA = new byte[0];

  // Transport used to communicate with an Oak Launcher.
  private final T transport;
  private final byte[] serverEncryptionPublicKey;

  @Deprecated
  /**
   * Create an instance of the Oak Client by remotely attesting an Oak Enclave and creating an
   * encrypted channel.
   *
   * @param <E> type that implements interfaces for the transport and for the evidence provider.
   * @param <V> type that implements an interface for the attestation verifier.
   * @return an instance of the {@code OakClient} wrapped in a {@code Result}
   * @deprecated prefer the create method that accepts the clock explicitly
   */
  public static <E extends EvidenceProvider & Transport, V extends AttestationVerifier>
      Result<OakClient<E>, Exception> create(E transport, V verifier) {
    return create(transport, verifier, Clock.systemUTC());
  }

  /**
   * Create an instance of the Oak Client by remotely attesting an Oak Enclave and creating an
   * encrypted channel.
   *
   * @param <E> type that implements interfaces for the transport and for the evidence provider.
   * @param <V> type that implements an interface for the attestation verifier.
   * @return an instance of the {@code OakClient} wrapped in a {@code Result}
   */
  public static <E extends EvidenceProvider & Transport, V extends AttestationVerifier>
      Result<OakClient<E>, Exception> create(E transport, V verifier, Clock clock) {
    // TODO(#3641): Implement client-side attestation verification.
    return transport.getEndorsedEvidence()
        .mapError(Exception::new)
        .andThen(endorsedEvidence
            -> verifier
                   .verify(clock.instant(), endorsedEvidence.getEvidence(),
                       endorsedEvidence.getEndorsements())
                   .andThen(b -> {
                     if (b.getStatus() == AttestationResults.Status.STATUS_SUCCESS) {
                       return Result.success(
                           new OakClient<E>(transport, b.getEncryptionPublicKey().toByteArray()));
                     } else {
                       return Result.error(new IllegalStateException(
                           "Couldn't verify attestation results: " + b.getReason()));
                     }
                   }));
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
  public Result<byte[], Exception> invoke(byte[] requestBody) {
    return ClientEncryptor.create(this.serverEncryptionPublicKey)
        .andThen(encryptor
            // Encrypt request.
            -> encryptor
                   .encrypt(requestBody, EMPTY_ASSOCIATED_DATA)
                   // Send request.
                   .andThen(r -> this.transport.invoke(r).mapError(Exception::new))
                   // Decrypt response.
                   .andThen(encryptor::decrypt))
        .map(d -> d.plaintext);
  }

  @Override
  public void close() throws Exception {
    transport.close();
  }
}

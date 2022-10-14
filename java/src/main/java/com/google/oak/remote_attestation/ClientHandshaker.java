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

import com.google.common.base.VerifyException;
import com.google.common.hash.Hashing;
import com.google.common.primitives.Bytes;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.security.GeneralSecurityException;
import java.util.Random;
import java.util.logging.Level;
import java.util.logging.Logger;

/** Remote attestation protocol handshake implementation. */
public class ClientHandshaker {
  private static final Logger logger = Logger.getLogger(ClientHandshaker.class.getName());
  /** Size (in bytes) of a random array sent in messages to prevent replay attacks. */
  private static final int REPLAY_PROTECTION_ARRAY_LENGTH = 32;

  public static enum State {
    INITIALIZING,
    EXPECTING_SERVER_IDENTITY,
    COMPLETED,
    ABORTED,
  }

  /** Expected value of the server's TEE measurement. */
  private final byte[] expectedTeeMeasurement;
  /** Current state of the remote attestation protocol. */
  private State state;
  /**
   * Collection of previously sent and received messages. Signed transcript is sent in messages to
   * prevent replay attacks.
   */
  private byte[] transcript;
  /** Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation. */
  private final KeyNegotiator keyNegotiator;
  /** Encryptor that was created during the attestation handshake. */
  private AeadEncryptor encryptor;

  public ClientHandshaker(byte[] expectedTeeMeasurement) {
    this.expectedTeeMeasurement = expectedTeeMeasurement;
    state = State.INITIALIZING;
    transcript = new byte[0];
    // Generate client private/public key pair.
    keyNegotiator = new KeyNegotiator();
    encryptor = null;
  }

  /**
   * Initializes the remote attestation handshake by creating an {@code ClientHello} message.
   *
   * <p>Transitions {@code ClientHandshaker} state from {@code State.INITIALIZING} to {@code
   * State.EXPECTING_SERVER_IDENTITY} state.
   */
  public byte[] createClientHello() throws IOException {
    try {
      if (state != State.INITIALIZING) {
        throw new IllegalStateException("ClientHandshaker is not in the INITIALIZING state");
      }

      // Random vector sent in messages for preventing replay attacks.
      byte[] random = new byte[REPLAY_PROTECTION_ARRAY_LENGTH];
      new Random().nextBytes(random);

      // Create client hello message.
      Message.ClientHello clientHello = new Message.ClientHello(random);

      // Update current transcript.
      byte[] serializedClientHello = clientHello.serialize();
      appendTranscript(serializedClientHello);

      state = State.EXPECTING_SERVER_IDENTITY;
      return serializedClientHello;
    } catch (Exception e) {
      state = State.ABORTED;
      throw e;
    }
  }

  /**
   * Responds to {@code ServerIdentity} message by creating a {@code ClientIdentity} message and
   * derives session keys for encrypting/decrypting messages from the server. {@code ClientIdentity}
   * message contains an ephemeral public key for negotiating session keys.
   *
   * <p>Transitions {@code ClientHandshaker} state from {@code State.EXPECTING_SERVER_IDENTITY} to
   * {@code State.Attested} state.
   */
  public byte[] processServerIdentity(byte[] serializedServerIdentity)
      throws RuntimeException, IOException, GeneralSecurityException {
    try {
      if (state != State.EXPECTING_SERVER_IDENTITY) {
        throw new IllegalStateException(
            "ClientHandshaker is not in the EXPECTING_SERVER_IDENTITY state");
      }

      Message.ServerIdentity serverIdentity =
          Message.ServerIdentity.deserialize(serializedServerIdentity);

      // Update current transcript.
      // Transcript doesn't include transcript signature from the server identity message.
      Message.ServerIdentity serverIdentityNoSignature = new Message.ServerIdentity(
          serverIdentity.getEphemeralPublicKey(), serverIdentity.getRandom(),
          serverIdentity.getSigningPublicKey(), serverIdentity.getAttestationReport());
      byte[] serializedServerIdentityNoSignature = serverIdentityNoSignature.serialize();
      appendTranscript(serializedServerIdentityNoSignature);

      // Verify server transcript signature.
      byte[] transcriptHash = Hashing.sha256().hashBytes(transcript).asBytes();
      SignatureVerifier verifier = new SignatureVerifier(serverIdentity.getSigningPublicKey());
      if (!verifier.verify(transcriptHash, serverIdentity.getTranscriptSignature())) {
        throw new VerifyException("Couldn't verify server transcript signature");
      }

      // Verify server attestation info.
      if (!verifyAttestationInfo(serverIdentity)) {
        throw new VerifyException("Couldn't verify attestation info");
      }

      // Create client attestation identity.
      Message.ClientIdentity clientIdentity =
          new Message.ClientIdentity(keyNegotiator.getPublicKey(),
              // TODO(#2918): Actually instantiate a public key and sign transcript with it.
              // Signing public key.
              new byte[0],
              // Attestation report.
              new byte[0]);

      // Update current transcript.
      byte[] serializedClientIdentity = clientIdentity.serialize();
      transcript = Bytes.concat(transcript, serializedClientIdentity);

      // Agree on session keys and create an encryptor.
      encryptor = keyNegotiator.createEncryptor(
          serverIdentity.getEphemeralPublicKey(), KeyNegotiator.EncryptorType.CLIENT);

      state = State.COMPLETED;
      return serializedClientIdentity;
    } catch (Exception e) {
      state = State.ABORTED;
      throw e;
    }
  }

  /** Returns current state of the {@code ClientHandshaker}. */
  public State getState() {
    return state;
  }

  /** Returns an encryptor created based on the negotiated ephemeral keys. */
  public AeadEncryptor getEncryptor() throws RuntimeException {
    if (state != State.COMPLETED) {
      throw new IllegalStateException("ClientHandshaker is not in the COMPLETED state");
    }

    return encryptor;
  }

  // TODO(#2356): Change the return type to `VerificationResult`.
  // TODO(#2420): Make sure the implementation is consistent with that in the Rust client.
  /**
   * Verifies the validity of the attestation info:
   *
   * <p>
   *
   * <ul>
   *   <li>Checks that the TEE report is signed by TEE Provider’s root key.
   *   <li>Checks that the public key hash from the TEE report is equal to the hash of the public
   *       key presented in the server response.
   *   <li>Extracts the TEE measurement from the TEE report and compares it to the field {@code
   *       expectedTeeMeasurement}.
   * </ul>
   *
   * <p>
   */
  private Boolean verifyAttestationInfo(Message.ServerIdentity serverIdentity) throws IOException {
    // Generate expected attested data by calculating the SHA256 hash of the public key and the
    // signing key.
    byte[] ephemeralPublicKeyHash = sha256(serverIdentity.getEphemeralPublicKey());
    byte[] signingPublicKeyHash = sha256(serverIdentity.getSigningPublicKey());
    byte[] buffer = ByteBuffer.allocate(ephemeralPublicKeyHash.length + signingPublicKeyHash.length)
                        .put(ephemeralPublicKeyHash)
                        .put(signingPublicKeyHash)
                        .array();
    byte[] expectedAttestedData = sha256(buffer);

    // Verify attestationReport.
    if (!verifyRemoteAttestationReport(
            serverIdentity.getAttestationReport(), expectedAttestedData)) {
      logger.log(Level.WARNING, "Invalid remote attestation report");
      return false;
    }

    // TODO(#1867): Add remote attestation support.
    return true;
  }

  private boolean verifyRemoteAttestationReport(
      byte[] attestationReport, byte[] expectedAttestedData) {
    // TODO(#2917): Implement this method.
    return true;
  }

  private byte[] sha256(byte[] value) {
    return Hashing.sha256().hashBytes(value).asBytes();
  }

  /**
   * Appends {@code serializedMessage} to the protocol transcript. The protocol transcript is a
   * concatenation of all sent and received messages, which is used for preventing replay attacks.
   */
  private void appendTranscript(byte[] serializedMessage) {
    transcript = Bytes.concat(transcript, serializedMessage);
  }
}

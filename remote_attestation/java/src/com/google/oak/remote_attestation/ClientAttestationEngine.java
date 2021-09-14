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
import com.google.oak.remote_attestation.AeadEncryptor;
import com.google.oak.remote_attestation.KeyNegotiator;
import com.google.oak.remote_attestation.Message;
import com.google.oak.remote_attestation.Message.ServerIdentity;
import com.google.oak.remote_attestation.SignatureVerifier;
import com.google.protobuf.ByteString;
import java.io.IOException;
import java.security.GeneralSecurityException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Random;
import oak.remote_attestation.AttestationInfo;
import oak.remote_attestation.AttestationReport;

enum AttestationState {
  Initializing {
    @Override
    public AttestationState transition() {
      return Attesting;
    }
  },
  Attesting {
    @Override
    public AttestationState transition() {
      return Attested;
    }
  },
  Attested {
    @Override
    public AttestationState transition() {
      return this;
    }
  };

  public abstract AttestationState transition();
}

/** Remote attestation protocol handshake implementation. */
public class ClientAttestationEngine {
  /** Remote attestation protocol version. */
  private static final int ATTESTATION_PROTOCOL_VERSION = 1;
  /** Size (in bytes) of a random array sent in messages to prevent replay attacks. */
  private static final int REPLAY_PROTECTION_ARRAY_LENGTH = 32;
  /** Test value of the server's TEE measurement. */
  private static final String TEST_TEE_MEASUREMENT = "Test TEE measurement";

  /** Expected value of the server's TEE measurement. */
  private final byte[] expectedTeeMeasurement;
  /** Current state of the remote attestation protocol. */
  private AttestationState state;
  /**
   * Collection of previously sent and received messages.
   * Signed transcript is sent in messages to prevent replay attacks.
   */
  private byte[] transcript;
  /** Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation. */
  private final KeyNegotiator keyNegotiator;
  /** Encryptor that was created during the attestation handshake. */
  private AeadEncryptor encryptor;

  public ClientAttestationEngine(byte[] expectedTeeMeasurement) {
    this.expectedTeeMeasurement = expectedTeeMeasurement;
    state = AttestationState.Initializing;
    transcript = new byte[0];
    // Generate client private/public key pair.
    keyNegotiator = new KeyNegotiator();
    encryptor = null;
  }

  /**
   * Initializes the Remote Attestation handshake by creating an {@code ClientHello} message.
   *
   * Transitions {@code ClientAttestationEngine} state from {@code Initializing} to
   * {@code Attesting} state.
   */
  public byte[] createClientHello() throws IllegalStateException, IOException {
    if (state != AttestationState.Initializing) {
      throw new IllegalStateException("ClientAttestationEngine is not in the Initializing state");
    }

    // Random vector sent in messages for preventing replay attacks.
    byte[] random = new byte[REPLAY_PROTECTION_ARRAY_LENGTH];
    new Random().nextBytes(random);

    // Create client hello message.
    Message.ClientHello clientHello = new Message.ClientHello(random);

    // Update current transcript.
    byte[] serializedClientHello = clientHello.serialize();
    appendTranscript(serializedClientHello);

    state = state.transition();
    return serializedClientHello;
  }

  /**
   * Responds to {@code ServerIdentity} message by creating a {@code ClientIdentity} message and
   * derives session keys for encrypting/decrypting messages from the server.
   * {@code ClientIdentity} message contains an ephemeral public key for negotiating session keys.
   *
   * Transitions {@code AttestationEngine} state from {@code Attesting} to {@code Attested} state.
   */
  public byte[] processServerIdentity(byte[] serializedServerIdentity)
      throws IllegalStateException, IOException, GeneralSecurityException {
    if (state != AttestationState.Attesting) {
      throw new IllegalStateException("ClientAttestationEngine is not in the Attesting state");
    }

    Message.ServerIdentity serverIdentity =
        Message.ServerIdentity.deserialize(serializedServerIdentity);

    // Update current transcript.
    // Transcript doesn't include transcript signature from the server identity message.
    ServerIdentity serverIdentityNoSignature = new Message.ServerIdentity(
        serverIdentity.getEphemeralPublicKey(), serverIdentity.getRandom(),
        serverIdentity.getSigningPublicKey(), serverIdentity.getAttestationInfo());
    byte[] serializedServerIdentityNoSignature = serverIdentityNoSignature.serialize();
    appendTranscript(serializedServerIdentityNoSignature);

    // Verify server transcript signature.
    byte[] transcriptHash = Hashing.sha256().hashBytes(transcript).asBytes();
    SignatureVerifier verifier = new SignatureVerifier(serverIdentity.getSigningPublicKey());
    if (!verifier.verify(transcriptHash, serverIdentity.getTranscriptSignature())) {
      throw new VerifyException("Couldn't verify server transcript signature");
    }

    // Verify server attestation info.
    if (!verifyAttestationInfo(serverIdentity.getAttestationInfo())) {
      throw new VerifyException("Couldn't verify attestation info");
    }

    // Create client attestation identity.
    Message.ClientIdentity clientIdentity = new Message.ClientIdentity(keyNegotiator.getPublicKey(),
        // Signing public key.
        new byte[0],
        // Attestation info.
        new byte[0]);

    // Update current transcript.
    byte[] serializedClientIdentity = clientIdentity.serialize();
    transcript = Bytes.concat(transcript, serializedClientIdentity);

    // Agree on session keys and create an encryptor.
    encryptor = keyNegotiator.createEncryptor(
        serverIdentity.getEphemeralPublicKey(), KeyNegotiator.EncryptorType.CLIENT);

    state = state.transition();
    return serializedClientIdentity;
  }

  /** Returns an encryptor created based on the negotiated ephemeral keys. */
  public AeadEncryptor getEncryptor() {
    if (state != AttestationState.Attested) {
      throw new IllegalStateException("ClientAttestationEngine is not in the Attested state");
    }

    return encryptor;
  }

  /**
   * Verifies the validity of the attestation info:
   * - Checks that the TEE report is signed by TEE Provider’s root key.
   * - Checks that the public key hash from the TEE report is equal to the hash of the public key
   *   presented in the server response.
   * - Extracts the TEE measurement from the TEE report and compares it to the
   *   {@code expectedTeeMeasurement}.
   */
  private Boolean verifyAttestationInfo(byte[] serializedAttestationInfo) throws IOException {
    AttestationInfo attestationInfo = AttestationInfo.parseFrom(serializedAttestationInfo);

    // TODO(#1867): Add remote attestation support.
    return Arrays.equals(
        expectedTeeMeasurement, attestationInfo.getReport().getMeasurement().toByteArray());
  }

  /**
   * Appends {@code serializedMessage} to the protocol transcript.
   * Transcript is a concatenation of all sent and received messages, which is used for preventing
   * replay attacks.
   */
  private void appendTranscript(byte[] serializedMessage) {
    transcript = Bytes.concat(transcript, serializedMessage);
  }
}

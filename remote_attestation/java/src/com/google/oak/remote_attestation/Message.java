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

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;

/** Wrapper class for remote attestation protocol messages. */
public class Message {
  static final int CLIENT_HELLO_HEADER = 1;
  static final int SERVER_IDENTITY_HEADER = 2;
  static final int CLIENT_IDENTITY_HEADER = 3;
  static final int ENCRYPTED_DATA_HEADER = 4;

  /** Remote attestation protocol version. */
  public static final int PROTOCOL_VERSION = 1;
  /**
   * Size (in bytes) of the prefix that describes the size of a serialized array.
   * Prefix is encoded with Little-Endian.
   */
  public static final int ARRAY_SERIALIZATION_PREFIX_LENGTH = 8;

  public static final int NONCE_LENGTH = 12;
  /** Size (in bytes) of a random array sent in messages to prevent replay attacks. */
  public static final int REPLAY_PROTECTION_ARRAY_LENGTH = 32;
  public static final int EPHEMERAL_PUBLIC_KEY_LENGTH = 32;
  // TODO(#2277): Use OpenSSL signature format (which is 72 bytes).
  public static final int TRANSCRIPT_SIGNATURE_LENGTH = 64;
  public static final int SIGNING_PUBLIC_KEY_LENGTH = 65;

  private Message() {}

  /** Initial message that starts remote attestation handshake. */
  public static class ClientHello {
    /** Message header. */
    private final byte header;
    /** Random vector sent in messages for preventing replay attacks. */
    private final byte[] random;

    public ClientHello(byte[] random) {
      header = CLIENT_HELLO_HEADER;
      this.random = random;
    }

    public byte[] getRandom() {
      return random;
    }

    public byte[] serialize() throws IOException {
      ByteArrayOutputStream output = new ByteArrayOutputStream();
      DataOutputStream outputStream = new DataOutputStream(output);

      outputStream.writeByte(header);
      writeFixedSizeArray(outputStream, random, REPLAY_PROTECTION_ARRAY_LENGTH, "random value");
      outputStream.flush();

      return output.toByteArray();
    }

    public static ClientHello deserialize(byte[] input)
        throws IllegalArgumentException, IOException {
      DataInputStream inputStream = new DataInputStream(new ByteArrayInputStream(input));

      byte header = inputStream.readByte();
      if (header != CLIENT_HELLO_HEADER) {
        throw new IllegalArgumentException("Incorrect client hello message header");
      }

      byte[] random =
          readFixedSizeArray(inputStream, REPLAY_PROTECTION_ARRAY_LENGTH, "random value");

      return new Message.ClientHello(random);
    }
  }

  /**
   * Server identity message containing remote attestation information and a public key for
   * Diffie-Hellman key negotiation.
   */
  public static class ServerIdentity {
    /** Message header. */
    private final byte header;
    /** Remote attestation protocol version. */
    private final byte version;
    /** Public key needed to establish a session key. */
    private final byte[] ephemeralPublicKey;
    /** Random vector sent in messages for preventing replay attacks. */
    private final byte[] random;
    /**
     * Signature of the SHA-256 hash of all previously sent and received messages.
     * Transcript signature is sent in messages to prevent replay attacks.
     *
     * Signature must be an IEEE-P1363 encoded ECDSA-P256 signature.
     * https://datatracker.ietf.org/doc/html/rfc6979
     * https://standards.ieee.org/standard/1363-2000.html
     */
    private byte[] transcriptSignature;
    /**
     * Public key used to sign transcripts.
     *
     * Public key must be an OpenSSL ECDSA-P256 key, which is represented as
     * `0x04 | X: 32-byte | Y: 32-byte`.
     * Where X and Y are big-endian coordinates of an Elliptic Curve point.
     * https://datatracker.ietf.org/doc/html/rfc6979
     */
    private final byte[] signingPublicKey;
    /**
     * Information used for remote attestation such as a TEE report and a TEE provider's
     * certificate. TEE report contains a hash of the `signingPublicKey`.
     *
     * Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
     * message.
     */
    private final byte[] attestationInfo;
    /* Additional info to be checked when verifying the identity. This may include server
     * configuration details, and inclusion proofs on a verifiable log (e.g., LogEntry on Rekor).
     * The server and the client must be able to agree on a canonical representation of the
     * content to be able to deterministically compute the hash of this field.
     */
    private final byte[] additionalInfo;

    public ServerIdentity(byte[] ephemeralPublicKey, byte[] random, byte[] signingPublicKey,
        byte[] attestationInfo, byte[] additionalInfo) {
      header = SERVER_IDENTITY_HEADER;
      version = PROTOCOL_VERSION;
      this.ephemeralPublicKey = ephemeralPublicKey;
      this.random = random;
      this.transcriptSignature = new byte[0];
      this.signingPublicKey = signingPublicKey;
      this.attestationInfo = attestationInfo;
      this.additionalInfo = additionalInfo;
    }

    public byte getVersion() {
      return version;
    }

    public byte[] getEphemeralPublicKey() {
      return ephemeralPublicKey;
    }

    public byte[] getRandom() {
      return random;
    }

    public byte[] getTranscriptSignature() {
      return transcriptSignature;
    }

    public void setTranscriptSignature(byte[] transcriptSignature) {
      this.transcriptSignature = transcriptSignature;
    }

    public byte[] getSigningPublicKey() {
      return signingPublicKey;
    }

    public byte[] getAttestationInfo() {
      return attestationInfo;
    }

    public byte[] getAdditionalInfo() {
      return additionalInfo;
    }

    public byte[] serialize() throws IOException {
      ByteArrayOutputStream output = new ByteArrayOutputStream();
      DataOutputStream outputStream = new DataOutputStream(output);

      outputStream.writeByte(header);
      outputStream.writeByte(version);
      writeFixedSizeArray(
          outputStream, ephemeralPublicKey, EPHEMERAL_PUBLIC_KEY_LENGTH, "ephemeral public key");
      writeFixedSizeArray(outputStream, random, REPLAY_PROTECTION_ARRAY_LENGTH, "random value");
      writeFixedSizeArray(
          outputStream, transcriptSignature, TRANSCRIPT_SIGNATURE_LENGTH, "transcript signature");
      writeFixedSizeArray(
          outputStream, signingPublicKey, SIGNING_PUBLIC_KEY_LENGTH, "signing public key");
      writeVariableSizeArray(outputStream, attestationInfo, "attestation info");
      writeVariableSizeArray(outputStream, additionalInfo, "additional info");
      outputStream.flush();

      return output.toByteArray();
    }

    public static ServerIdentity deserialize(byte[] input)
        throws IllegalArgumentException, IOException {
      DataInputStream inputStream = new DataInputStream(new ByteArrayInputStream(input));

      byte header = inputStream.readByte();
      if (header != SERVER_IDENTITY_HEADER) {
        throw new IllegalArgumentException("Incorrect server identity message header");
      }

      byte version = inputStream.readByte();
      if (version != PROTOCOL_VERSION) {
        throw new IllegalArgumentException("Incorrect remote attestation protocol version");
      }

      byte[] ephemeralPublicKey =
          readFixedSizeArray(inputStream, EPHEMERAL_PUBLIC_KEY_LENGTH, "ephemeral public key");
      byte[] random =
          readFixedSizeArray(inputStream, REPLAY_PROTECTION_ARRAY_LENGTH, "random value");
      byte[] transcriptSignature =
          readFixedSizeArray(inputStream, TRANSCRIPT_SIGNATURE_LENGTH, "transcript signature");
      byte[] signingPublicKey =
          readFixedSizeArray(inputStream, SIGNING_PUBLIC_KEY_LENGTH, "signing key");
      byte[] attestationInfo = readVariableSizeArray(inputStream, "attestation info");
      byte[] additionalInfo = readVariableSizeArray(inputStream, "additional info");

      ServerIdentity serverIdentity = new ServerIdentity(
          ephemeralPublicKey, random, signingPublicKey, attestationInfo, additionalInfo);
      serverIdentity.setTranscriptSignature(transcriptSignature);
      return serverIdentity;
    }
  }

  /**
   * Client identity message containing remote attestation information and a public key for
   * Diffie-Hellman key negotiation.
   */
  public static class ClientIdentity {
    /** Message header. */
    private final byte header;
    /** Public key needed to establish a session key. */
    private final byte[] ephemeralPublicKey;
    /**
     * Signature of the SHA-256 hash of all previously sent and received messages.
     * Transcript signature is sent in messages to prevent replay attacks.
     *
     * Signature must be an IEEE-P1363 encoded ECDSA-P256 signature.
     * https://datatracker.ietf.org/doc/html/rfc6979
     * https://standards.ieee.org/standard/1363-2000.html
     */
    private byte[] transcriptSignature;
    /**
     * Public key used to sign transcripts.
     *
     * Public key must be an OpenSSL ECDSA-P256 key, which is represented as
     * `0x04 | X: 32-byte | Y: 32-byte`.
     * Where X and Y are big-endian coordinates of an Elliptic Curve point.
     * https://datatracker.ietf.org/doc/html/rfc6979
     */
    private final byte[] signingPublicKey;
    /**
     * Information used for remote attestation such as a TEE report and a TEE provider's
     * certificate. TEE report contains a hash of the `signingPublicKey`.
     *
     * Attestation info must be a serialized `oak.remote_attestation.AttestationInfo` Protobuf
     * message.
     */
    private final byte[] attestationInfo;

    public ClientIdentity(
        byte[] ephemeralPublicKey, byte[] signingPublicKey, byte[] attestationInfo) {
      header = CLIENT_IDENTITY_HEADER;
      this.ephemeralPublicKey = ephemeralPublicKey;
      this.transcriptSignature = new byte[0];
      this.signingPublicKey = signingPublicKey;
      this.attestationInfo = attestationInfo;
    }

    public byte[] getEphemeralPublicKey() {
      return ephemeralPublicKey;
    }

    public byte[] getTranscriptSignature() {
      return transcriptSignature;
    }

    public void setTranscriptSignature(byte[] transcriptSignature) {
      this.transcriptSignature = transcriptSignature;
    }

    public byte[] getSigningPublicKey() {
      return signingPublicKey;
    }

    public byte[] getAttestationInfo() {
      return attestationInfo;
    }

    public byte[] serialize() throws IOException {
      ByteArrayOutputStream output = new ByteArrayOutputStream();
      DataOutputStream outputStream = new DataOutputStream(output);

      outputStream.writeByte(header);
      writeFixedSizeArray(
          outputStream, ephemeralPublicKey, EPHEMERAL_PUBLIC_KEY_LENGTH, "ephemeral public key");
      writeFixedSizeArray(
          outputStream, transcriptSignature, TRANSCRIPT_SIGNATURE_LENGTH, "transcript signature");
      writeFixedSizeArray(
          outputStream, signingPublicKey, SIGNING_PUBLIC_KEY_LENGTH, "signing public key");
      writeVariableSizeArray(outputStream, attestationInfo, "attestation info");
      outputStream.flush();

      return output.toByteArray();
    }

    public static ClientIdentity deserialize(byte[] input)
        throws IllegalArgumentException, IOException {
      DataInputStream inputStream = new DataInputStream(new ByteArrayInputStream(input));

      byte header = inputStream.readByte();
      if (header != CLIENT_IDENTITY_HEADER) {
        throw new IllegalArgumentException("Incorrect client hello message header");
      }

      byte[] ephemeralPublicKey =
          readFixedSizeArray(inputStream, EPHEMERAL_PUBLIC_KEY_LENGTH, "ephemeral public key");
      byte[] transcriptSignature =
          readFixedSizeArray(inputStream, TRANSCRIPT_SIGNATURE_LENGTH, "transcript signature");
      byte[] signingPublicKey =
          readFixedSizeArray(inputStream, SIGNING_PUBLIC_KEY_LENGTH, "signing key");
      byte[] attestationInfo = readVariableSizeArray(inputStream, "attestation info");

      ClientIdentity clientIdentity =
          new ClientIdentity(ephemeralPublicKey, signingPublicKey, attestationInfo);
      clientIdentity.setTranscriptSignature(transcriptSignature);
      return clientIdentity;
    }
  }

  /** Message containing data encrypted using a session key. */
  public static class EncryptedData {
    /** Message header. */
    private final byte header;
    /** Random nonce (initialization vector) used for encryption/decryption. */
    private final byte[] nonce;
    /** Data encrypted using the session key. */
    private final byte[] data;

    public EncryptedData(byte[] nonce, byte[] data) {
      header = ENCRYPTED_DATA_HEADER;
      this.nonce = nonce;
      this.data = data;
    }

    public byte[] getNonce() {
      return nonce;
    }

    public byte[] getData() {
      return data;
    }

    public byte[] serialize() throws IOException {
      ByteArrayOutputStream output = new ByteArrayOutputStream();
      DataOutputStream outputStream = new DataOutputStream(output);

      outputStream.writeByte(header);
      writeFixedSizeArray(outputStream, nonce, NONCE_LENGTH, "nonce");
      writeVariableSizeArray(outputStream, data, "data");
      outputStream.flush();

      return output.toByteArray();
    }

    public static EncryptedData deserialize(byte[] input)
        throws IllegalArgumentException, IOException {
      DataInputStream inputStream = new DataInputStream(new ByteArrayInputStream(input));

      byte header = inputStream.readByte();
      if (header != ENCRYPTED_DATA_HEADER) {
        throw new IllegalArgumentException("Incorrect encrypted data message header");
      }

      byte[] nonce = readFixedSizeArray(inputStream, NONCE_LENGTH, "nonce");
      byte[] data = readVariableSizeArray(inputStream, "data");

      EncryptedData encryptedData = new EncryptedData(nonce, data);
      return encryptedData;
    }
  }

  private static byte[] readFixedSizeArray(DataInputStream inputStream, int size, String name)
      throws IOException {
    byte[] input = new byte[size];
    try {
      inputStream.readFully(input, 0, size);
    } catch (IOException e) {
      throw new IOException("Couldn't read " + name + " from input stream", e);
    }
    return input;
  }

  private static byte[] readVariableSizeArray(DataInputStream inputStream, String name)
      throws IllegalArgumentException, IOException {
    byte[] sizeBytes =
        readFixedSizeArray(inputStream, ARRAY_SERIALIZATION_PREFIX_LENGTH, name + " size");
    int size = ByteBuffer.wrap(sizeBytes).order(ByteOrder.LITTLE_ENDIAN).getInt();
    return readFixedSizeArray(inputStream, size, name);
  }

  private static void writeFixedSizeArray(DataOutputStream outputStream, byte[] value, int size,
      String name) throws IllegalArgumentException, IOException {
    if (size > 0) {
      if (value.length == 0 || value.length == size) {
        try {
          byte[] outputValue = (value.length == 0) ? new byte[size] : value;
          outputStream.write(outputValue, 0, size);
        } catch (IOException e) {
          throw new IOException("Couldn't write " + name + " to output stream", e);
        }
      } else {
        throw new IllegalArgumentException(
            "Incorrect " + name + " size, expected " + size + ", found " + value.length);
      }
    }
  }

  private static void writeVariableSizeArray(DataOutputStream outputStream, byte[] value,
      String name) throws IllegalArgumentException, IOException {
    long outputSize = (long) value.length;
    byte[] outputSizeBytes = ByteBuffer.allocate(ARRAY_SERIALIZATION_PREFIX_LENGTH)
                                 .order(ByteOrder.LITTLE_ENDIAN)
                                 .putLong(outputSize)
                                 .array();
    writeFixedSizeArray(
        outputStream, outputSizeBytes, ARRAY_SERIALIZATION_PREFIX_LENGTH, name + " size");
    writeFixedSizeArray(outputStream, value, value.length, name);
  }
}

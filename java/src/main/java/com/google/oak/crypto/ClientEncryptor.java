//
// Copyright 2023 The Project Oak Authors
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

package com.google.oak.crypto;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.oak.crypto.hpke.Hpke;
import com.google.oak.crypto.hpke.SenderContext;
import com.google.oak.crypto.v1.AeadEncryptedMessage;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import com.google.protobuf.ExtensionRegistry;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.Optional;

/**
 * Encryptor class for encrypting client requests that will be sent to the server and decrypting
 * server responses that are received by the client. Each Encryptor corresponds to a single crypto
 * session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ClientEncryptor implements AutoCloseable, Encryptor {
  // Info string used by Hybrid Public Key Encryption.
  private static final byte[] OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1".getBytes(UTF_8);

  // Encapsulated public key needed to establish a symmetric session key.
  // Only sent in the initial request message of the session.
  private boolean serializedEncapsulatedPublicKeyHasBeenSent;
  private final SenderContext senderContext;

  /**
   * Creates a new instance of {@code ClientEncryptor}.
   * The corresponding encryption and decryption keys are generated using the server public key with
   * Hybrid Public Key Encryption (HPKE).
   * <https://www.rfc-editor.org/rfc/rfc9180.html>.
   *
   * @param serializedServerPublicKey a NIST P-256 SEC1 encoded point public key; see
   * <https://secg.org/sec1-v2.pdf>
   */
  public static final Result<ClientEncryptor, Exception> create(
      final byte[] serializedServerPublicKey) {
    return Hpke.setupBaseSender(serializedServerPublicKey, OAK_HPKE_INFO).map(ClientEncryptor::new);
  }

  /**
   * Cleans up resources allocated by sender contexts.
   */
  @Override
  public void close() {
    senderContext.close();
  }

  private ClientEncryptor(SenderContext senderContext) {
    this.serializedEncapsulatedPublicKeyHasBeenSent = false;
    this.senderContext = senderContext;
  }

  /**
   * Encrypts `plaintext` and authenticates `associatedData` using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param plaintext the input byte array to be encrypted
   * @param associatedData the input byte array with associated data to be authenticated
   * @return a serialized {@code EncryptedRequest} message wrapped in a {@code Result}
   */
  @Override
  public final Result<byte[], Exception> encrypt(
      final byte[] plaintext, final byte[] associatedData) {
    // Encrypt request.
    return senderContext.seal(plaintext, associatedData).map(ciphertext -> {
      // Create request message.
      EncryptedRequest.Builder encryptedRequestBuilder =
          EncryptedRequest.newBuilder().setEncryptedMessage(
              AeadEncryptedMessage.newBuilder()
                  .setCiphertext(ByteString.copyFrom(ciphertext))
                  .setAssociatedData(ByteString.copyFrom(associatedData))
                  .build());

      // Encapsulated public key is only sent in the initial request message of the session.
      if (!serializedEncapsulatedPublicKeyHasBeenSent) {
        encryptedRequestBuilder.setSerializedEncapsulatedPublicKey(
            ByteString.copyFrom(senderContext.getSerializedEncapsulatedPublicKey()));
        serializedEncapsulatedPublicKeyHasBeenSent = true;
      }

      // TODO(#3843): Return unserialized proto messages once we have Java encryption without
      // JNI.
      return encryptedRequestBuilder.build().toByteArray();
    });
  }

  /**
   * Decrypts a {@code EncryptedResponse} proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param serializedEncryptedResponse a serialized {@code EncryptedResponse} message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  @Override
  public final Result<Encryptor.DecryptionResult, Exception> decrypt(
      final byte[] serializedEncryptedResponse) {
    // Deserialize response message.
    EncryptedResponse encryptedResponse;
    try {
      encryptedResponse = EncryptedResponse.parseFrom(
          serializedEncryptedResponse, ExtensionRegistry.getEmptyRegistry());
    } catch (InvalidProtocolBufferException e) {
      return Result.error(e);
    }
    AeadEncryptedMessage aeadEncryptedMessage = encryptedResponse.getEncryptedMessage();
    byte[] ciphertext = aeadEncryptedMessage.getCiphertext().toByteArray();
    byte[] associatedData = aeadEncryptedMessage.getAssociatedData().toByteArray();

    // Decrypt response.
    return senderContext.open(ciphertext, associatedData)
        .map(plaintext
            ->
            // TODO(#3843): Accept unserialized proto messages once we have Java encryption without
            // JNI.
            new DecryptionResult(plaintext, associatedData));
  }
}

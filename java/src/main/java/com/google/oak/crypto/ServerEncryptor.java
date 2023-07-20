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

import com.google.oak.crypto.hpke.Context;
import com.google.oak.crypto.hpke.Hpke;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.v1.AeadEncryptedMessage;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import com.google.protobuf.ExtensionRegistry;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.Optional;

/**
 * Encryptor class for decrypting client requests that are received by the server and encrypting
 * server responses that will be sent back to the client. Each Encryptor corresponds to a single
 * crypto session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ServerEncryptor implements AutoCloseable, Encryptor {
  // Info string used by Hybrid Public Key Encryption.
  private static final byte[] OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1".getBytes(UTF_8);

  private final KeyPair serverKeyPair;

  // Contexts are initialized after receiving an initial request messagecontaining client's
  // encapsulated public key.
  private Optional<Context.RecipientRequestContext> recipientRequestContext;
  private Optional<Context.RecipientResponseContext> recipientResponseContext;

  /**
   * Creates a new instance of {@code ServerEncryptor}.
   *
   * @param serverKeyPair key pair used to create the recipient context.
   */
  public ServerEncryptor(KeyPair serverKeyPair) {
    this.serverKeyPair = serverKeyPair;
    this.recipientRequestContext = Optional.empty();
    this.recipientResponseContext = Optional.empty();
  }

  /**
   * Cleans up resources allocated by recipient contexts.
   */
  @Override
  public void close() {
    if (this.recipientRequestContext.isPresent()) {
      this.recipientRequestContext.get().close();
      this.recipientRequestContext = Optional.empty();
    }
    if (this.recipientResponseContext.isPresent()) {
      this.recipientResponseContext.get().close();
      this.recipientResponseContext = Optional.empty();
    }
  }

  /**
   * Decrypts a {@code com.google.oak.crypto.v1.EncryptedRequest} proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param serializedEncryptedRequest a serialized {@code
   *     com.google.oak.crypto.v1.EncryptedRequest} message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  @Override
  public final Result<Encryptor.DecryptionResult, Exception> decrypt(
      final byte[] serializedEncryptedRequest) {
    // Deserialize request message.
    EncryptedRequest encryptedRequest;
    try {
      encryptedRequest = EncryptedRequest.parseFrom(
          serializedEncryptedRequest, ExtensionRegistry.getEmptyRegistry());
    } catch (InvalidProtocolBufferException e) {
      return Result.error(e);
    }
    AeadEncryptedMessage aeadEncryptedMessage = encryptedRequest.getEncryptedMessage();
    byte[] ciphertext = aeadEncryptedMessage.getCiphertext().toByteArray();
    byte[] associatedData = aeadEncryptedMessage.getAssociatedData().toByteArray();

    // Get recipient context.
    if (this.recipientRequestContext.isEmpty()) {
      // Get serialized encapsulated public key.
      if (encryptedRequest.getSerializedEncapsulatedPublicKey().equals(ByteString.EMPTY)) {
        return Result.error(new Exception(
            "serialized encapsulated public key is not present in the initial request message"));
      }
      byte[] serializedEncapsulatedPublicKey =
          encryptedRequest.getSerializedEncapsulatedPublicKey().toByteArray();

      // Create recipient context.
      Result<Hpke.RecipientContext, Exception> setupBaseRecipientResult = Hpke.setupBaseRecipient(
          serializedEncapsulatedPublicKey, this.serverKeyPair, OAK_HPKE_INFO);

      this.recipientRequestContext =
          setupBaseRecipientResult.success().map(r -> r.recipientRequestContext);
      this.recipientResponseContext =
          setupBaseRecipientResult.success().map(r -> r.recipientResponseContext);
    }
    Context.RecipientRequestContext recipientRequestContext = this.recipientRequestContext.get();

    // Decrypt request.
    return recipientRequestContext.open(ciphertext, associatedData)
        .map(plaintext
            ->
            // TODO(#3843): Accept unserialized proto messages once we have Java encryption
            // without JNI.
            new Encryptor.DecryptionResult(plaintext, associatedData));
  }

  /**
   * Encrypts `plaintext` and authenticates `associatedData` using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param plaintext the input byte array to be encrypted
   * @param associatedData the input byte array with associated data to be authenticated
   * @return a serialized {@code com.google.oak.crypto.v1.EncryptedResponse} message wrapped in a
   *     {@code Result}
   */
  @Override
  public final Result<byte[], Exception> encrypt(
      final byte[] plaintext, final byte[] associatedData) {
    // Get recipient context.
    if (this.recipientResponseContext.isEmpty()) {
      return Result.error(new Exception("server encryptor is not initialized"));
    }
    Context.RecipientResponseContext recipientResponseContext = this.recipientResponseContext.get();

    // Encrypt response.
    return recipientResponseContext
        .seal(plaintext, associatedData)
        // Create response message.
        .map(ciphertext
            -> EncryptedResponse.newBuilder()
                   .setEncryptedMessage(AeadEncryptedMessage.newBuilder()
                                            .setCiphertext(ByteString.copyFrom(ciphertext))
                                            .setAssociatedData(ByteString.copyFrom(associatedData))
                                            .build())
                   .build()
                   .toByteArray());
  }
}

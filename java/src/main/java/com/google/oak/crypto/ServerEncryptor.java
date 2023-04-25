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

import com.google.oak.crypto.hpke.Context;
import com.google.oak.crypto.hpke.Hpke;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.Optional;
import oak.crypto.AeadEncryptedMessage;
import oak.crypto.EncryptedRequest;
import oak.crypto.EncryptedResponse;

/**
 * Encryptor class for decrypting client requests that are received by the server and encrypting
 * server responses that will be sent back to the client. Each Encryptor corresponds to a single
 * crypto session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ServerEncryptor implements Encryptor {
  // Info string used by Hybrid Public Key Encryption.
  private static final byte[] OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1".getBytes();

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
  // TODO(#3642): Implement Java Hybrid Encryption.
  public ServerEncryptor(KeyPair serverKeyPair) {
    this.serverKeyPair = serverKeyPair;
    this.recipientRequestContext = Optional.empty();
    this.recipientResponseContext = Optional.empty();
  }

  /**
   * Decrypts a {@code EncryptedRequest} proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param encryptedRequest a serialized {@code EncryptedRequest} message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  @Override
  public final Result<Encryptor.DecryptionResult, Exception> decrypt(
      final byte[] serializedEncryptedRequest) {
    // Deserialize request message.
    EncryptedRequest encryptedRequest;
    try {
      encryptedRequest = EncryptedRequest.parseFrom(serializedEncryptedRequest);
    } catch (InvalidProtocolBufferException e) {
      return Result.error(e);
    }
    AeadEncryptedMessage aeadEncryptedMessage = encryptedRequest.getEncryptedMessage();
    byte[] ciphertext = aeadEncryptedMessage.getCiphertext().toByteArray();
    byte[] associatedData = aeadEncryptedMessage.getAssociatedData().toByteArray();

    // Get recipient context;
    if (!this.recipientRequestContext.isPresent()) {
      // Get serialized encapsulated public key.
      if (encryptedRequest.getSerializedEncapsulatedPublicKey()
          == com.google.protobuf.ByteString.EMPTY) {
        return Result.error(new Exception(
            "serialized encapsulated public key is not present in the initial request message"));
      }
      byte[] serializedEncapsulatedPublicKey =
          encryptedRequest.getSerializedEncapsulatedPublicKey().toByteArray();

      // Create recipient context.
      Result<Hpke.RecipientContext, Exception> setupBaseRecipientResult = Hpke.setupBaseRecipient(
          serializedEncapsulatedPublicKey, this.serverKeyPair, OAK_HPKE_INFO);
      if (setupBaseRecipientResult.isError()) {
        return Result.error(setupBaseRecipientResult.error().get());
      }
      Hpke.RecipientContext recipientContext = setupBaseRecipientResult.success().get();

      this.recipientRequestContext = Optional.of(recipientContext.recipientRequestContext);
      this.recipientResponseContext = Optional.of(recipientContext.recipientResponseContext);
    }
    Context.RecipientRequestContext recipientRequestContext = this.recipientRequestContext.get();

    // Decrypt request.
    Result<byte[], Exception> openResult = recipientRequestContext.open(ciphertext, associatedData);
    if (openResult.isError()) {
      return Result.error(openResult.error().get());
    }
    byte[] plaintext = openResult.success().get();

    // TODO(#3843): Accept unserialized proto messages once we have Java encryption without JNI.
    return Result.success(new Encryptor.DecryptionResult(plaintext, associatedData));
  }

  /**
   * Encrypts `plaintext` and authenticates `associatedData` using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param plaintext the input byte array to be encrypted
   * @param associatedData the input byte array with associated data to be authenticated
   * @return a serialized {@code EncryptedResponse} message wrapped in a {@code Result}
   */
  @Override
  public final Result<byte[], Exception> encrypt(
      final byte[] plaintext, final byte[] associatedData) {
    // Get recipient context;
    if (!this.recipientResponseContext.isPresent()) {
      return Result.error(new Exception("server encryptor is not initialized"));
    }
    Context.RecipientResponseContext recipientResponseContext = this.recipientResponseContext.get();

    // Encrypt response.
    Result<byte[], Exception> sealResult = recipientResponseContext.seal(plaintext, associatedData);
    if (sealResult.isError()) {
      return Result.error(sealResult.error().get());
    }
    byte[] ciphertext = sealResult.success().get();

    // Create response message.
    EncryptedResponse encryptedResponse =
        EncryptedResponse.newBuilder()
            .setEncryptedMessage(AeadEncryptedMessage.newBuilder()
                                     .setCiphertext(ByteString.copyFrom(ciphertext))
                                     .setAssociatedData(ByteString.copyFrom(associatedData))
                                     .build())
            .build();

    // TODO(#3843): Return unserialized proto messages once we have Java encryption without JNI.
    return Result.success(encryptedResponse.toByteArray());
  }
}

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

import com.google.oak.crypto.DecryptionResult;
import com.google.oak.crypto.hpke.Hpke;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.hpke.RecipientContext;
import com.google.oak.crypto.v1.AeadEncryptedMessage;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import java.util.Optional;

/**
 * Encryptor class for decrypting client requests that are received by the server and encrypting
 * server responses that will be sent back to the client. Each Encryptor corresponds to a single
 * crypto session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ServerEncryptor implements AutoCloseable {
  // Info string used by Hybrid Public Key Encryption.
  private static final byte[] OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1".getBytes(UTF_8);

  private final KeyPair serverKeyPair;

  // Context is initialized after receiving an initial request messagecontaining client's
  // encapsulated public key.
  private Optional<RecipientContext> recipientContext;

  /**
   * Creates a new instance of {@code ServerEncryptor}.
   *
   * @param serverKeyPair key pair used to create the recipient context.
   */
  public ServerEncryptor(KeyPair serverKeyPair) {
    this.serverKeyPair = serverKeyPair;
    this.recipientContext = Optional.empty();
  }

  /**
   * Cleans up resources allocated by recipient contexts.
   */
  @Override
  public void close() {
    if (recipientContext.isPresent()) {
      recipientContext.get().close();
      recipientContext = Optional.empty();
    }
  }

  /**
   * Decrypts a {@code com.google.oak.crypto.v1.EncryptedRequest} proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param encryptedRequest {@code EncryptedRequest} proto message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  public final Result<DecryptionResult, Exception> decrypt(
      final EncryptedRequest encryptedRequest) {
    AeadEncryptedMessage aeadEncryptedMessage = encryptedRequest.getEncryptedMessage();
    byte[] ciphertext = aeadEncryptedMessage.getCiphertext().toByteArray();
    byte[] associatedData = aeadEncryptedMessage.getAssociatedData().toByteArray();

    // Get recipient context.
    if (recipientContext.isEmpty()) {
      // Get serialized encapsulated public key.
      if (encryptedRequest.getSerializedEncapsulatedPublicKey().equals(ByteString.EMPTY)) {
        return Result.error(new Exception(
            "serialized encapsulated public key is not present in the initial request message"));
      }
      byte[] serializedEncapsulatedPublicKey =
          encryptedRequest.getSerializedEncapsulatedPublicKey().toByteArray();

      // Create recipient context.
      Result<RecipientContext, Exception> setupBaseRecipientResult =
          Hpke.setupBaseRecipient(serializedEncapsulatedPublicKey, serverKeyPair, OAK_HPKE_INFO);

      recipientContext = setupBaseRecipientResult.success();
    }

    // Decrypt request.
    return recipientContext.get()
        .open(ciphertext, associatedData)
        .map(plaintext -> new DecryptionResult(plaintext, associatedData));
  }

  /**
   * Encrypts `plaintext` and authenticates `associatedData` using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param plaintext the input byte array to be encrypted
   * @param associatedData the input byte array with associated data to be authenticated
   * @return {@code EncryptedResponse} proto message wrapped in a {@code Result}
   */
  public final Result<EncryptedResponse, Exception> encrypt(
      final byte[] plaintext, final byte[] associatedData) {
    // Get recipient context.
    if (recipientContext.isEmpty()) {
      return Result.error(new Exception("server encryptor is not initialized"));
    }

    // Encrypt response.
    return recipientContext.get().generateNonce().map(nonce
        -> recipientContext.get()
               .seal(plaintext, associatedData)
               // Create response message.
               .map(ciphertext
                   -> EncryptedResponse.newBuilder()
                          .setEncryptedMessage(
                              AeadEncryptedMessage.newBuilder()
                                  .setNonce(ByteString.copyFrom(nonce))
                                  .setCiphertext(ByteString.copyFrom(ciphertext))
                                  .setAssociatedData(ByteString.copyFrom(associatedData))
                                  .build())
                          .build()));
  }
}

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

import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import com.google.protobuf.InvalidProtocolBufferException;
import java.io.IOException;
import java.security.GeneralSecurityException;
import oak.crypto.AeadEncryptedMessage;
import oak.crypto.EncryptedRequest;
import oak.crypto.EncryptedResponse;

/**
 * Encryptor class for encrypting client requests that will be sent to the server and decrypting
 * server responses that are received by the client. Each Encryptor object corresponds to a
 * single crypto session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ClientEncryptor implements Encryptor {
  // TODO(#3642): Remove this key and use a real encapsulated key generated by the client once Java
  // encryption is implemented.
  private static final byte[] TEST_ENCAPSULATED_PUBLIC_KEY = {4, 61, (byte) 141, 127, (byte) 160,
      (byte) 162, (byte) 184, (byte) 158, 72, (byte) 237, 105, 64, (byte) 182, 118, (byte) 163,
      (byte) 183, (byte) 174, 1, 81, 66, (byte) 139, 37, (byte) 218, (byte) 208, 17, (byte) 139,
      (byte) 159, (byte) 158, 68, 123, 124, 96, 114, (byte) 150, 38, (byte) 251, 112, 28, 121,
      (byte) 132, 45, (byte) 250, 118, (byte) 208, (byte) 142, (byte) 153, 124, (byte) 192,
      (byte) 139, (byte) 178, (byte) 239, (byte) 188, (byte) 177, (byte) 219, 52, (byte) 178, 123,
      117, (byte) 254, (byte) 171, (byte) 248, 77, 4, (byte) 242, 118};

  // Info string used by Hybrid Public Key Encryption.
  private static final String OAK_HPKE_INFO = "Oak Hybrid Public Key Encryption v1";

  private final byte[] serializedServerPublicKey;

  /**
   * Creates a new instance of [`ClientEncryptor`].
   *
   * @param serializedServerPublicKey a NIST P-256 SEC1 encoded point public key.
   * <https://secg.org/sec1-v2.pdf>
   */
  public ClientEncryptor(final byte[] serializedServerPublicKey) {
    this.serializedServerPublicKey = serializedServerPublicKey;
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
    // TODO(#3843): Return unserialized proto messages once we have Java encryption without JNI.
    // TODO(#3642): Implement Java Hybrid Encryption.
    EncryptedRequest encryptedRequest =
        EncryptedRequest.newBuilder()
            .setEncryptedMessage(AeadEncryptedMessage.newBuilder()
                                     .setCiphertext(ByteString.copyFrom(plaintext))
                                     .setAssociatedData(ByteString.copyFrom(associatedData))
                                     .build())
            .setSerializedEncapsulatedPublicKey(ByteString.copyFrom(TEST_ENCAPSULATED_PUBLIC_KEY))
            .build();
    return Result.success(encryptedRequest.toByteArray());
  }

  /**
   * Decrypts a [`EncryptedResponse`] proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param encryptedResponse a serialized {@code EncryptedResponse} message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  @Override
  public final Result<Encryptor.DecryptionResult, Exception> decrypt(
      final byte[] encryptedResponse) {
    // TODO(#3843): Accept unserialized proto messages once we have Java encryption without JNI.
    // TODO(#3642): Implement Java Hybrid Encryption.
    try {
      AeadEncryptedMessage aeadEncryptedMessage =
          EncryptedResponse.parseFrom(encryptedResponse).getEncryptedMessage();
      byte[] plaintext = aeadEncryptedMessage.getCiphertext().toByteArray();
      byte[] associatedData = aeadEncryptedMessage.getAssociatedData().toByteArray();
      return Result.success(new ClientEncryptor.DecryptionResult(plaintext, associatedData));
    } catch (InvalidProtocolBufferException e) {
      return Result.error(e);
    }
  }
}

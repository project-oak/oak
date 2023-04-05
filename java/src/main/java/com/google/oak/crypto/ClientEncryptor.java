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
import java.io.IOException;
import java.security.GeneralSecurityException;

/**
 * Encryptor class for encrypting client requests that will be sent to the server and decrypting
 * server responses that are received by the client. Each Encryptor object corresponds to a
 * single crypto session between the client and the server.
 *
 * Sequence numbers for requests and responses are incremented separately, meaning that there could
 * be multiple responses per request and multiple requests per response.
 */
public class ClientEncryptor {
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
  public final Result<byte[], Exception> encrypt(
      final byte[] plaintext, final byte[] associatedData) {
    // TODO(#3843): Return unserialized proto messages once we have Java encryption without JNI.
    // TODO(#3642): Implement Java Hybrid Encryption.
    return Result.success(new byte[0]);
  }

  public static final class DecryptionResult {
    public final byte[] plaintext;
    public final byte[] associatedData;

    public DecryptionResult(byte[] plaintext, byte[] associatedData) {
      this.plaintext = plaintext;
      this.associatedData = associatedData;
    }
  }

  /**
   * Decrypts a [`EncryptedResponse`] proto message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param encryptedResponse a serialized {@code EncryptedResponse} message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  public final Result<DecryptionResult, Exception> decrypt(final byte[] encryptedResponse) {
    // TODO(#3843): Accept unserialized proto messages once we have Java encryption without JNI.
    // TODO(#3642): Implement Java Hybrid Encryption.
    return Result.success(new ClientEncryptor.DecryptionResult(new byte[0], new byte[0]));
  }
}

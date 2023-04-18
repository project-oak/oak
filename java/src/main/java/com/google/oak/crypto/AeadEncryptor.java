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

/**
 * Interface representing an encryptor for Authenticated Encryption with Associated Data (AEAD).
 * <https://datatracker.ietf.org/doc/html/rfc5116>
 */
public interface AeadEncryptor {
  public static final class DecryptionResult {
    public final byte[] plaintext;
    public final byte[] associatedData;

    public DecryptionResult(byte[] plaintext, byte[] associatedData) {
      this.plaintext = plaintext;
      this.associatedData = associatedData;
    }
  }

  /**
   * Encrypts `plaintext` and authenticates `associatedData` using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param plaintext the input byte array to be encrypted
   * @param associatedData the input byte array with associated data to be authenticated
   * @return a serialized encrypted message wrapped in a {@code Result}
   */
  Result<byte[], Exception> encrypt(final byte[] plaintext, final byte[] associatedData);

  /**
   * Decrypts a serialized encrypted message using AEAD.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   *
   * @param encryptedMessage a serialized encrypted message
   * @return a response message plaintext and associated data wrapped in a {@code Result}
   */
  Result<DecryptionResult, Exception> decrypt(final byte[] encryptedMessage);
}

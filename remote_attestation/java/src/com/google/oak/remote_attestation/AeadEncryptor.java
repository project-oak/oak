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

import com.google.common.primitives.Bytes;
import com.google.crypto.tink.subtle.AesGcmJce;
import com.google.oak.remote_attestation.Message;
import java.io.IOException;
import java.security.GeneralSecurityException;
import java.util.Arrays;

/**
 * Implementation of Authenticated Encryption with Associated Data (AEAD).
 * https://datatracker.ietf.org/doc/html/rfc5116
 *
 * This implementation uses separate keys for encrypting data and decrypting peer encrypted data.
 * Which means that this implementation uses the same key for encryption, which peer uses for
 * decryption.
 * It is necessary to prevent the Loopback Attack, where malicious network takes an outgoing packet
 * and feeds it back as an incoming packet.
 */
public class AeadEncryptor {
  private final AesGcmJce encryptor;
  private final AesGcmJce decryptor;

  public AeadEncryptor(byte[] encryptionKey, byte[] decryptionKey) throws GeneralSecurityException {
    encryptor = new AesGcmJce(encryptionKey);
    decryptor = new AesGcmJce(decryptionKey);
  }

  /**
   * Encrypts {@code data} using {@code AeadEncryptor::encryptor}.
   * Encrypted data is prefixed with a random 12 bit nonce.
   * @return a serialized {@code Message.EncryptedData}.
   */
  public byte[] encrypt(byte[] data) throws GeneralSecurityException, IOException {
    // Additional authenticated data is not required for the remotely attested channel,
    // since after session key is established client and server exchange messages with a
    // single encrypted field.
    byte[] result = encryptor.encrypt(data, null);

    byte[] nonce = Arrays.copyOf(result, Message.NONCE_LENGTH);
    byte[] encryptedData = Arrays.copyOfRange(result, Message.NONCE_LENGTH, result.length);
    return new Message.EncryptedData(nonce, encryptedData).serialize();
  }

  /**
   * Decrypts and authenticates {@code data} using {@code AeadEncryptor::encryptor}.
   * @param data is a serialized {@code Message.EncryptedData}.
   */
  public byte[] decrypt(byte[] data) throws GeneralSecurityException, IOException {
    Message.EncryptedData deserializedData = Message.EncryptedData.deserialize(data);

    // Create a byte array prefixed with a 12 bit nonce.
    byte[] prefixedData = Bytes.concat(deserializedData.getNonce(), deserializedData.getData());

    // Additional authenticated data is not required for the remotely attested channel,
    // since after session key is established client and server exchange messages with a
    // single encrypted field.
    return decryptor.decrypt(prefixedData, null);
  }
}

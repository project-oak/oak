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

package com.google.oak.remote_attestation.crypto;

import com.google.protobuf.ByteString;
import java.lang.IllegalArgumentException;
import java.security.GeneralSecurityException;
import java.security.SecureRandom;
import java.util.Arrays;
import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.GCMParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import oak.remote_attestation.EncryptedData;

/**
 * Implementation of Authenticated Encryption with Associated Data (AEAD).
 * https://datatracker.ietf.org/doc/html/rfc5116
 */
public class AeadEncryptor {
    private static final String ENCRYPTION_ALGORITHM = "AES";
    private static final String AEAD_ALGORITHM = "AES/GCM/NoPadding";
    private static final int KEY_LENGTH_BITS = 256;
    private static final int TAG_LENGTH_BITS = 128;
    private static final int NONCE_LENGTH_BYTES = 12;

    private final SecretKey key;

    public AeadEncryptor(byte[] key) {
        if (key.length * 8 != KEY_LENGTH_BITS) {
            throw new IllegalArgumentException(
                String.format("Incorrect key length: %d, expected %d", key.length * 8, KEY_LENGTH_BITS)
            );
        }
        this.key = new SecretKeySpec(key, 0, key.length, ENCRYPTION_ALGORITHM);
    }

    /**
     * Encrypts `data` using AES-GCM.
     * The resulting encrypted data contains a random 12 byte nonce.
     */
    public EncryptedData encrypt(byte[] data) throws GeneralSecurityException {
        Cipher encryptor = Cipher.getInstance(AEAD_ALGORITHM);

        // Create a random nonce.
        byte[] nonce = generateNonce(NONCE_LENGTH_BYTES);
        GCMParameterSpec gcmParameterSpecification = new GCMParameterSpec(TAG_LENGTH_BITS, nonce);

        // Initialize encryptor.
        encryptor.init(Cipher.ENCRYPT_MODE, key, gcmParameterSpecification);

        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        byte[] encryptedData = encryptor.doFinal(data);
        return EncryptedData.newBuilder()
                .setNonce(ByteString.copyFrom(nonce))
                .setData(ByteString.copyFrom(encryptedData))
                .build();
    }

    /**
     * Decrypts and authenticates `data` using AES-GCM.
     */
    public byte[] decrypt(EncryptedData data) throws GeneralSecurityException {
        Cipher decryptor = Cipher.getInstance(AEAD_ALGORITHM);

        byte[] nonce = data.getNonce().toByteArray();
        GCMParameterSpec gcmParameterSpecification = new GCMParameterSpec(TAG_LENGTH_BITS, nonce);

        // Initialize decryptor.
        decryptor.init(Cipher.DECRYPT_MODE, key, gcmParameterSpecification);

        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        byte[] encryptedData = data.getData().toByteArray();
        return decryptor.doFinal(encryptedData);
    }

    /**
     * Generates a random nonce.
     */
    static private byte[] generateNonce(int lengthBytes) {
        byte[] nonce = new byte[lengthBytes];
        SecureRandom random = new SecureRandom();
        random.nextBytes(nonce);
        return nonce;
    }
}

package com.google.oak.functions.client;

import com.google.oak.functions.client.Util;
import java.lang.IllegalArgumentException;
import java.security.GeneralSecurityException;
import java.security.SecureRandom;
import java.util.Arrays;
import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.GCMParameterSpec;
import javax.crypto.spec.SecretKeySpec;

/**
 * Implementation of Authenticated Encryption with Associated Data (AEAD).
 * https://datatracker.ietf.org/doc/html/rfc5116
 */
public class AeadEncryptor {
    private static String ENCRYPTION_ALGORITHM = "AES";
    private static String AEAD_ALGORITHM = "AES/GCM/NoPadding";
    private static int KEY_LENGTH_BITS = 256;
    private static int TAG_LENGTH_BITS = 128;
    private static int INITIALIZATION_VECTOR_LENGTH_BYTES = 12;

    private SecretKey key;
    private SecretKeySpec keySpecification;

    public AeadEncryptor(byte[] key) throws IllegalArgumentException {
        if (key.length * 8 != KEY_LENGTH_BITS) {
            throw new IllegalArgumentException(
                String.format("Incorrect key length: %d, expected %d", key.length * 8, KEY_LENGTH_BITS)
            );
        }
        this.key = new SecretKeySpec(key, 0, key.length, AEAD_ALGORITHM);
        this.keySpecification = new SecretKeySpec(this.key.getEncoded(), ENCRYPTION_ALGORITHM);
    }

    /**
     * Encrypts `data` using AES-GCM.
     * The resulting encrypted data is prefixed with a random 12 bit nonce.
     */
    public byte[] encrypt(byte[] data) throws GeneralSecurityException {
        Cipher encryptor = Cipher.getInstance(AEAD_ALGORITHM);

        // Create a random initialization vector.
        byte[] initializationVector = generateInitializationVector(INITIALIZATION_VECTOR_LENGTH_BYTES);
        GCMParameterSpec gcmParameterSpecification = new GCMParameterSpec(TAG_LENGTH_BITS, initializationVector);

        // Initialize encryptor.
        encryptor.init(Cipher.ENCRYPT_MODE, this.keySpecification, gcmParameterSpecification);

        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        byte[] encryptedData = encryptor.doFinal(data);

        // Add `initializationVector` as a prefix to the `encryptedData`.
        return Util.concatenate(initializationVector, encryptedData);
    }

    /**
     * Decrypts and authenticates `data` using AES-GCM.
     * `data` must contain an encrypted message prefixed with a 12 bit nonce.
     */
    public byte[] decrypt(byte[] data) throws GeneralSecurityException {
        Cipher decryptor = Cipher.getInstance(AEAD_ALGORITHM);

        // Extract initialization vector from `data`.
        byte[] initializationVector = Arrays.copyOfRange(data, 0, INITIALIZATION_VECTOR_LENGTH_BYTES );
        GCMParameterSpec gcmParameterSpecification = new GCMParameterSpec(TAG_LENGTH_BITS, initializationVector);

        // Initialize decryptor.
        decryptor.init(Cipher.DECRYPT_MODE, this.keySpecification, gcmParameterSpecification);

        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        byte[] encryptedData = Arrays.copyOfRange(data, INITIALIZATION_VECTOR_LENGTH_BYTES, data.length);
        return decryptor.doFinal(encryptedData);
    }

    /**
     * Generates a random initialization vector.
     */
    private byte[] generateInitializationVector(int lengthBytes) {
        byte[] initializationVector = new byte[lengthBytes];
        SecureRandom random = new SecureRandom();
        random.nextBytes(initializationVector);
        return initializationVector;
    }
}

package com.google.oak.grpc_attestation_client;

import com.google.crypto.tink.subtle.AesGcmJce;
import java.security.GeneralSecurityException;

/**
 * Implementation of Authenticated Encryption with Associated Data (AEAD).
 * https://datatracker.ietf.org/doc/html/rfc5116
 */
public class AeadEncryptor {
    private AesGcmJce encryptor;

    public AeadEncryptor(byte[] key) throws GeneralSecurityException {
        // TODO(#2120): Use a wrapper AEAD interface and don't use `tink.subtle`.
        this.encryptor = new AesGcmJce(key);
    }

    /**
     * Encrypts `data` using `AeadEncryptor::encryptor`.
     * The resulting encrypted data is prefixed with a random 12 bit nonce.
     */
    public byte[] encrypt(byte[] data) throws GeneralSecurityException {
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        return this.encryptor.encrypt(data, null);
    }

    /**
     * Decrypts and authenticates `data` using `AeadEncryptor::encryptor`.
     * `data` must contain an encrypted message prefixed with a 12 bit nonce.
     */
    public byte[] decrypt(byte[] data) throws GeneralSecurityException {
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        return this.encryptor.decrypt(data, null);
    }
}

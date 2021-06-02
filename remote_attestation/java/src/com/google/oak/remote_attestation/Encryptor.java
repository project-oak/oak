package com.google.oak.remote_attestation;

import com.google.oak.remote_attestation.crypto.AeadEncryptor;
import java.security.GeneralSecurityException;

/** Wrapper for `com.google.oak.remote_attestation.AeadEncryptor`. */
public class Encryptor {
    private final AeadEncryptor encryptor;

    protected Encryptor(AeadEncryptor encryptor) {
        this.encryptor = encryptor;
    }

    public byte[] encrypt(byte[] data) throws GeneralSecurityException {
        return encryptor.encrypt(data);
    }

    public byte[] decrypt(byte[] data) throws GeneralSecurityException {
        return encryptor.decrypt(data);
    }
}

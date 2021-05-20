package com.google.oak.grpc_attestation_client;

import com.google.crypto.tink.subtle.AesGcmJce;
import java.security.GeneralSecurityException;

public class AeadEncryptor {
    private AesGcmJce encryptor;

    public AeadEncryptor(byte[] key) throws GeneralSecurityException {
        this.encryptor = new AesGcmJce(key);
    }

    public byte[] encrypt(byte[] data) throws GeneralSecurityException {
        return this.encryptor.encrypt(data, new byte[0]);
    }

    public byte[] decrypt(byte[] data) throws GeneralSecurityException {
        return this.encryptor.decrypt(data, new byte[0]);
    }
}



package com.google.oak.functions.client;

import com.google.oak.functions.client.AeadEncryptor;
import com.google.crypto.tink.subtle.X25519;
import java.security.GeneralSecurityException;
import java.security.InvalidKeyException;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
    private byte[] privateKey;

    public KeyNegotiator() {
        this.privateKey = X25519.generatePrivateKey();
    }

    public byte[] getPublicKey() throws InvalidKeyException {
        return X25519.publicFromPrivate(this.privateKey);
    }

    /** Derives a session key from `peerPublicKey` and `KeyNegotiator::privateKey`. */
    public byte[] deriveSessionKey(byte[] peerPublicKey) throws InvalidKeyException {
        // TODO(#2100): Derive session key using a KDF.
        // https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        return X25519.computeSharedSecret(this.privateKey, peerPublicKey);
    }

    /** Derives a session key and creates an `AeadEncryptor::encryptor` from it */
    public AeadEncryptor createAeadEncryptor(byte[] peerPublicKey) throws InvalidKeyException, GeneralSecurityException {
        byte[] sessionKey = this.deriveSessionKey(peerPublicKey);
        return new AeadEncryptor(sessionKey);
    }
}

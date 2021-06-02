package com.google.oak.remote_attestation.crypto;

import com.google.crypto.tink.subtle.X25519;
import java.security.GeneralSecurityException;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
    private final byte[] privateKey;

    public KeyNegotiator() {
        privateKey = X25519.generatePrivateKey();
    }

    public byte[] getPublicKey() throws GeneralSecurityException {
        return X25519.publicFromPrivate(privateKey);
    }

    /** Derives a session key from `peerPublicKey` and `KeyNegotiator::privateKey`. */
    public byte[] deriveSessionKey(byte[] peerPublicKey) throws GeneralSecurityException {
        // TODO(#2100): Derive session key using a KDF.
        // https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        return X25519.computeSharedSecret(privateKey, peerPublicKey);
    }

    /** Derives a session key and creates an `AeadEncryptor::encryptor` from it */
    public AeadEncryptor createAeadEncryptor(byte[] peerPublicKey) throws GeneralSecurityException {
        byte[] sessionKey = deriveSessionKey(peerPublicKey);
        return new AeadEncryptor(sessionKey);
    }
}

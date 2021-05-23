package com.google.oak.grpc_attestation_client;

import com.google.crypto.tink.subtle.X25519;
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
}

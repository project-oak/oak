package com.google.oak.functions.client;

import com.google.oak.functions.client.AeadEncryptor;
import java.security.GeneralSecurityException;
import java.security.InvalidKeyException;
import java.security.KeyFactory;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.PublicKey;
import java.security.spec.X509EncodedKeySpec;
import javax.crypto.KeyAgreement;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
    private static String KEY_GENERATION_ALGORITHM = "EC";
    private static int KEY_LENGTH_BITS = 256;
    private static String KEY_AGREEMENT_ALGORITHM = "ECDH";

    KeyPair keyPair;

    public KeyNegotiator() throws GeneralSecurityException {
        KeyPairGenerator keyPairGenerator = KeyPairGenerator.getInstance(KEY_GENERATION_ALGORITHM);
        keyPairGenerator.initialize(KEY_LENGTH_BITS);
        this.keyPair = keyPairGenerator.generateKeyPair();
    }

    public byte[] getPublicKey() throws GeneralSecurityException {
        return keyPair.getPublic().getEncoded();
    }

    /** Derives a session key from `peerPublicKey` and `KeyNegotiator::privateKey`. */
    public byte[] deriveSessionKey(byte[] peerPublicKey) throws GeneralSecurityException {
        KeyFactory keyFactory = KeyFactory.getInstance(KEY_GENERATION_ALGORITHM);
        X509EncodedKeySpec keySpecification = new X509EncodedKeySpec(peerPublicKey);
        PublicKey parsedPeerPublicKey = keyFactory.generatePublic(keySpecification);

        KeyAgreement keyAgreement = KeyAgreement.getInstance(KEY_AGREEMENT_ALGORITHM);
        keyAgreement.init(this.keyPair.getPrivate());
        keyAgreement.doPhase(parsedPeerPublicKey, true);

        // TODO(#2100): Derive session key using a KDF.
        // https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        return keyAgreement.generateSecret();
    }

    /** Derives a session key and creates an `AeadEncryptor::encryptor` from it */
    public AeadEncryptor createAeadEncryptor(byte[] peerPublicKey) throws GeneralSecurityException {
        byte[] sessionKey = this.deriveSessionKey(peerPublicKey);
        return new AeadEncryptor(sessionKey);
    }
}

package com.google.oak.functions.client;

import com.google.oak.functions.client.AeadEncryptor;
import com.google.oak.functions.client.Util;
import java.security.GeneralSecurityException;
import java.security.KeyFactory;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.PublicKey;
import java.security.spec.X509EncodedKeySpec;
import java.util.Arrays;
import javax.crypto.KeyAgreement;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
    private static final String KEY_AGREEMENT_ALGORITHM = "X25519";
    private static final int ALGORITHM_IDENTIFIER_LENGTH_BYTES = 14;

    KeyPair keyPair;

    public KeyNegotiator() throws GeneralSecurityException {
        KeyPairGenerator keyPairGenerator = KeyPairGenerator.getInstance(KEY_AGREEMENT_ALGORITHM);
        keyPair = keyPairGenerator.generateKeyPair();
    }

    /**
     * Returns a `subjectPublicKey` bit string from an X.509 `SubjectPublicKeyInfo`.
     * https://datatracker.ietf.org/doc/html/rfc3280#section-4.1
     * */
    public byte[] getPublicKey() throws GeneralSecurityException {
        // Get a public key encoded as an X.509 `SubjectPublicKeyInfo`.
        byte[] publicKey = keyPair.getPublic().getEncoded();
        // Remove `AlgorithmIdentifier` from X.509 `SubjectPublicKeyInfo` and get `subjectPublicKey`
        // bit string.
        return Arrays.copyOfRange(publicKey, ALGORITHM_IDENTIFIER_LENGTH_BYTES, publicKey.length);
    }

    /**
     * Derives a session key from `peerPublicKey` and `KeyNegotiator::privateKey`.
     * `peerPublicKey` should be a `subjectPublicKey` bit string from an X.509
     * `SubjectPublicKeyInfo`.
     * https://datatracker.ietf.org/doc/html/rfc3280#section-4.1
     * */
    public byte[] deriveSessionKey(byte[] peerPublicKey) throws GeneralSecurityException {
        PublicKey parsedPeerPublicKey = parsePublicKey(peerPublicKey);

        KeyAgreement keyAgreement = KeyAgreement.getInstance(KEY_AGREEMENT_ALGORITHM);
        keyAgreement.init(keyPair.getPrivate());
        keyAgreement.doPhase(parsedPeerPublicKey, true);
        byte[] keyMaterial = keyAgreement.generateSecret();

        return keyDerivationFunction(keyMaterial, peerPublicKey);
    }

    /** Derives a session key and creates an `AeadEncryptor` from it. */
    public AeadEncryptor createAeadEncryptor(byte[] peerPublicKey) throws GeneralSecurityException {
        byte[] sessionKey = deriveSessionKey(peerPublicKey);
        return new AeadEncryptor(sessionKey);
    }

    /**
     * Parses a public key represented as a `subjectPublicKey` bit string from an X.509
     * `SubjectPublicKeyInfo`.
     * */
    private PublicKey parsePublicKey(byte[] publicKey) throws GeneralSecurityException {
        // Add an X.509 `AlgorithmIdentifier` prefix to the public key.
        byte[] algorithmIdentifier = getAlgorithmIdentifier();
        byte[] prefixedPublicKey = Util.concatenate(algorithmIdentifier, publicKey);
        X509EncodedKeySpec keySpecification = new X509EncodedKeySpec(prefixedPublicKey);

        // Parse public key.
        KeyFactory keyFactory = KeyFactory.getInstance(KEY_AGREEMENT_ALGORITHM);
        return keyFactory.generatePublic(keySpecification);
    }

    /** Returns an X.509 `AlgorithmIdentifier` bit string. */
    private byte[] getAlgorithmIdentifier() {
        PublicKey publicKey = keyPair.getPublic();
        return Arrays.copyOfRange(publicKey.getEncoded(), 0, ALGORITHM_IDENTIFIER_LENGTH_BYTES);
    }

    /** Derives a session key from `keyMaterial`. */
    private byte[] keyDerivationFunction(byte[] keyMaterial, byte[] peerPublicKey) {
        // TODO(#2100): Derive a session key not just from `keyMaterial` but also from server's and
        // client's public keys.
        // https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        return keyMaterial;
    }
}

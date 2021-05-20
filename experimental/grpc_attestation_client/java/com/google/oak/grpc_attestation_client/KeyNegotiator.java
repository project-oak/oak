package com.google.oak.grpc_attestation_client;

import com.google.crypto.tink.subtle.X25519;
import java.security.InvalidKeyException;
// import java.security.KeyFactory;
// import java.security.KeyPair;
// import java.security.KeyPairGenerator;
// import java.security.NoSuchAlgorithmException;
// import java.security.PublicKey;
// import javax.crypto.KeyAgreement;

// public class KeyNegotiator {
//     private KeyPair keyPair;

//     private static String keyPairGenerationAlgorithm = "X25519"; // "EC";
//     private static int keySize = 128;
//     private static String keyAgreementAlgorithm = "X25519"; // "ECDH";

//     public KeyNegotiator() throws NoSuchAlgorithmException, InvalidKeyException {
//         KeyPairGenerator keyPairGenerator = KeyPairGenerator.getInstance(keyPairGenerationAlgorithm);
//         keyPairGenerator.initialize(keySize);
//         this.keyPair = keyPairGenerator.generateKeyPair();
//     }

//     public byte[] getPublicKey() {
//         return this.keyPair.getPublic().getEncoded();
//     }

//     public byte[] deriveSessionKey(byte[] peerPublicKeyBytes) throws NoSuchAlgorithmException, InvalidKeyException {
//         PublicKey peerPublicKey = KeyPairGenerator.getInstance(keyPairGenerationAlgorithm).generatePublic(peerPublicKeyBytes);
//         KeyAgreement keyAgreement = KeyAgreement.getInstance(keyAgreementAlgorithm);
//         keyAgreement.init(this.keyPair.getPrivate());
//         keyAgreement.doPhase(publicKey, true);
//         byte[] sessionKey = keyAgreement.generateSecret();
//         return sessionKey;
//     }
// }

public class KeyNegotiator {
    private byte[] privateKey;

    public KeyNegotiator() {
        this.privateKey = X25519.generatePrivateKey();
    }

    public byte[] getPublicKey() throws InvalidKeyException {
        return X25519.publicFromPrivate(this.privateKey);
    }

    public byte[] deriveSessionKey(byte[] peerPublicKey) throws InvalidKeyException {
        return X25519.computeSharedSecret(this.privateKey, peerPublicKey);
    }
}

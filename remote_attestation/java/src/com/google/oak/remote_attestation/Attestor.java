package com.google.oak.remote_attestation;

import com.google.common.base.VerifyException;
import com.google.oak.remote_attestation.crypto.AeadEncryptor;
import com.google.oak.remote_attestation.crypto.KeyNegotiator;
import java.security.GeneralSecurityException;

/**
 * Performs remote attestation, key negotiation and data encryption/decryption based on the
 * negotiated key.
 */
public class Attestor {
    private final KeyNegotiator keyNegotiator;

    public Attestor() throws GeneralSecurityException {
        // Generate client private/public key pair.
        keyNegotiator = new KeyNegotiator();
    }

    /** Returns a Diffie-Hellman public key corresponding to the `keyNegotiator`. */
    public byte[] getPublicKey() throws GeneralSecurityException {
        return keyNegotiator.getPublicKey();
    }

    public Encryptor attest(byte[] peerPublicKey, byte[] peerAttestationInfo) throws GeneralSecurityException {
        if (!verifyAttestation(peerAttestationInfo)) {
            throw new VerifyException("Couldn't verify attestation info");
        }
        AeadEncryptor encryptor = keyNegotiator.createAeadEncryptor(peerPublicKey);
        return new Encryptor(encryptor);
    }

    private Boolean verifyAttestation(byte[] attestationInfo) {
        // TODO(#1867): Add remote attestation support.
        return true;
    }
}

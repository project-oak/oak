//
// Copyright 2021 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.remote_attestation;

import com.google.common.primitives.Bytes;
import com.google.crypto.tink.subtle.Hkdf;
import com.google.crypto.tink.subtle.X25519;
import java.security.GeneralSecurityException;
import java.util.Arrays;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
    // MAC algorithm used in HKDF.
    private static final String KEY_DERIVATION_ALGORITHM = "HMACSHA256";
    // Salt used for key derivation with HKDF.
    // https://datatracker.ietf.org/doc/html/rfc5869
    private static final String KEY_DERIVATION_SALT = "Remote Attestation Protocol v1";
    // Purpose string used for deriving session keys with HKDF.
    private static final String KEY_PURPOSE = "Remote Attestation Protocol Session Key";
    // AES-256 with GCM key size.
    // https://datatracker.ietf.org/doc/html/rfc5288
    private static final int KEY_SIZE_BYTES = 32;
    private final byte[] privateKey;

    public KeyNegotiator() {
        privateKey = X25519.generatePrivateKey();
    }

    public byte[] getPublicKey() throws GeneralSecurityException {
        return X25519.publicFromPrivate(privateKey);
    }

    /**
     * Derives a session key from `peerPublicKey` and `KeyNegotiator::privateKey`.
     * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
     * 
     * TODO(#2181): Use separate keys for server and client encryption.
     */
    public byte[] deriveSessionKey(byte[] peerPublicKey) throws GeneralSecurityException {
        // Session key is derived from a purpose string, public key and peer public key.
        byte[] info = KEY_PURPOSE.getBytes();
        // Sort public keys so that keys derived on the both sides of the protocol are equal.
        byte[] publicKey = getPublicKey();
        byte[] publicKeys = null;
        if (Arrays.compareUnsigned(publicKey, peerPublicKey) < 0) {
            publicKeys = Bytes.concat(publicKey, peerPublicKey);
        } else {
            publicKeys = Bytes.concat(peerPublicKey, publicKey);
        }
        info = Bytes.concat(info, publicKeys);

        // Derive session key.
        byte[] key_material = X25519.computeSharedSecret(privateKey, peerPublicKey);
        return Hkdf.computeHkdf(
            KEY_DERIVATION_ALGORITHM,
            key_material,
            KEY_DERIVATION_SALT.getBytes(),
            info,
            KEY_SIZE_BYTES
        );
    }

    /** Derives a session key and creates an `AeadEncryptor::encryptor` from it */
    public AeadEncryptor createAeadEncryptor(byte[] peerPublicKey) throws GeneralSecurityException {
        byte[] sessionKey = deriveSessionKey(peerPublicKey);
        return new AeadEncryptor(sessionKey);
    }
}

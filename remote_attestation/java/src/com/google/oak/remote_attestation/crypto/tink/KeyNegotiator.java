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

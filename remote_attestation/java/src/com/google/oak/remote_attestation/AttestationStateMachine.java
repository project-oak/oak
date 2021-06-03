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

import com.google.common.base.VerifyException;
import com.google.oak.remote_attestation.crypto.AeadEncryptor;
import com.google.oak.remote_attestation.crypto.KeyNegotiator;
import java.security.GeneralSecurityException;

public class AttestationStateMachine {
    /**
     * Performs remote attestation and key negotiation.
     */
    public static class Unattested {
        private final KeyNegotiator keyNegotiator;

        public Unattested() throws GeneralSecurityException {
            // Generate client private/public key pair.
            keyNegotiator = new KeyNegotiator();
        }

        /** Returns a Diffie-Hellman public key corresponding to the `keyNegotiator`. */
        public byte[] getPublicKey() throws GeneralSecurityException {
            return keyNegotiator.getPublicKey();
        }

        /**
         * Remotely attests a peer, agrees on the shared key and creates an
         * `AttestationStateMachine.Attested`.
         */
        public Attested attest(byte[] peerPublicKey, byte[] peerAttestationInfo) throws GeneralSecurityException {
            if (!verifyAttestation(peerAttestationInfo)) {
                throw new VerifyException("Couldn't verify attestation info");
            }
            AeadEncryptor encryptor = keyNegotiator.createAeadEncryptor(peerPublicKey);
            return new Attested(encryptor);
        }

        private Boolean verifyAttestation(byte[] attestationInfo) {
            // TODO(#1867): Add remote attestation support.
            return true;
        }
    }

    /**
     * Performs data encryption/decryption based on the negotiated key.
     */
    public static class Attested {
        private final AeadEncryptor encryptor;

        protected Attested(AeadEncryptor encryptor) {
            this.encryptor = encryptor;
        }

        public byte[] encrypt(byte[] data) throws GeneralSecurityException {
            return encryptor.encrypt(data);
        }

        public byte[] decrypt(byte[] data) throws GeneralSecurityException {
            return encryptor.decrypt(data);
        }
    }
}

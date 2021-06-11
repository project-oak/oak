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
import com.google.oak.remote_attestation.AeadEncryptor;
import com.google.oak.remote_attestation.KeyNegotiator;
import com.google.protobuf.ByteString;
import java.security.GeneralSecurityException;
import java.util.Arrays;
import oak.remote_attestation.AttestationIdentity;
import oak.remote_attestation.AttestationInfo;
import oak.remote_attestation.AttestationReport;
import oak.remote_attestation.EncryptedData;

public class AttestationStateMachine {
    /**
     * Performs remote attestation and key negotiation.
     */
    public static class Unattested {
        private static final String test_tee_measurement = "Test TEE measurement";
        private final byte[] expected_tee_measurement;
        private final KeyNegotiator keyNegotiator;

        public Unattested(byte[] expected_tee_measurement) throws GeneralSecurityException {
            this.expected_tee_measurement = expected_tee_measurement;
            // Generate client private/public key pair.
            keyNegotiator = new KeyNegotiator();
        }

        /** Returns an `AttestationIdentity` corresponding to the `keyNegotiator`. */
        public AttestationIdentity getIdentity() throws GeneralSecurityException {
            // Generate `AttestationInfo`.
            AttestationReport report = AttestationReport.newBuilder()
                    .setMeasurement(ByteString.copyFrom(test_tee_measurement.getBytes()))
                    .build();
            AttestationInfo attestationInfo = AttestationInfo.newBuilder()
                    .setReport(report)
                    .build();

            AttestationIdentity identity = AttestationIdentity.newBuilder()
                    .setPublicKey(ByteString.copyFrom(keyNegotiator.getPublicKey()))
                    .setAttestationInfo(attestationInfo)
                    .build();
            return identity;
        }

        /**
         * Remotely attests a peer, agrees on the shared key and creates an
         * `AttestationStateMachine.Attested`.
         */
        public Attested attest(AttestationIdentity peerIdentity) throws GeneralSecurityException {
            if (!verifyAttestation(peerIdentity.getAttestationInfo())) {
                throw new VerifyException("Couldn't verify attestation info");
            }
            AeadEncryptor encryptor =
                keyNegotiator.createAeadEncryptor(peerIdentity.getPublicKey().toByteArray());
            return new Attested(encryptor);
        }

        private Boolean verifyAttestation(AttestationInfo attestationInfo) {
            // TODO(#1867): Add remote attestation support.
            return Arrays.equals(
                expected_tee_measurement,
                attestationInfo.getReport().getMeasurement().toByteArray()
            );
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

        public EncryptedData encrypt(byte[] data) throws GeneralSecurityException {
            return encryptor.encrypt(data);
        }

        public byte[] decrypt(EncryptedData data) throws GeneralSecurityException {
            return encryptor.decrypt(data);
        }
    }
}

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

/** Remote attestation protocol implementation. */
public class AttestationEngine {
    private static final String test_tee_measurement = "Test TEE measurement";
    private final byte[] expected_tee_measurement;
    private final KeyNegotiator keyNegotiator;

    public AttestationEngine(byte[] expected_tee_measurement) throws GeneralSecurityException {
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
     * Verifies remote attestation, negotiates session keys and creates server [`AeadEncryptor`].
     *
     * Server encryptor uses server session key for encryption and client session key for
     * encryption.
     */
    public AeadEncryptor createServerEncryptor(AttestationIdentity peerIdentity) throws GeneralSecurityException {
        if (!verifyAttestation(peerIdentity.getAttestationInfo())) {
            throw new VerifyException("Couldn't verify attestation info");
        }
        return keyNegotiator.createEncryptor(
            peerIdentity.getPublicKey().toByteArray(),
            KeyNegotiator.EncryptorType.Server
        );
    }

    /**
     * Verifies remote attestation, negotiates session keys and creates client [`AeadEncryptor`].
     *
     * Client encryptor uses client session key for encryption and server session key for
     * encryption.
     */
    public AeadEncryptor createClientEncryptor(AttestationIdentity peerIdentity) throws GeneralSecurityException {
        if (!verifyAttestation(peerIdentity.getAttestationInfo())) {
            throw new VerifyException("Couldn't verify attestation info");
        }
        return keyNegotiator.createEncryptor(
            peerIdentity.getPublicKey().toByteArray(),
            KeyNegotiator.EncryptorType.Client
        );
    }

    private Boolean verifyAttestation(AttestationInfo attestationInfo) {
        // TODO(#1867): Add remote attestation support.
        return Arrays.equals(
            expected_tee_measurement,
            attestationInfo.getReport().getMeasurement().toByteArray()
        );
    }
}

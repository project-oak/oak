//
// Copyright 2023 The Project Oak Authors
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

package com.google.oak.transparency;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Base64;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class SignatureVerifierTest {
    private static final String SIGNATURE_PATH = "oak_remote_attestation_verification/testdata/endorsement.json.sig";
    private static final String PUBLIC_KEY_PATH = "oak_remote_attestation_verification/testdata/oak-development.pem";
    private static final String CONTENT_PATH = "oak_remote_attestation_verification/testdata/endorsement.json";

    private byte[] signatureBytes;
    private byte[] publicKeyBytes;
    private byte[] contentBytes;

    @Before
    public void setUp() throws Exception {
        signatureBytes = Files.readAllBytes(Path.of(SIGNATURE_PATH));
        publicKeyBytes = SignatureVerifier.convertPemToRaw(Files.readString(Path.of(PUBLIC_KEY_PATH)));
        contentBytes = Files.readAllBytes(Path.of(CONTENT_PATH));
    }

    @Test
    public void testVerifySucceeds() throws Exception {
        Optional<Failure> failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);

        Assert.assertFalse(failure.isPresent());
    }

    @Test
    public void testVerifyFailsWithManipulatedSignature() {
        signatureBytes[signatureBytes.length / 2]++;
        Optional<Failure> failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);

        Assert.assertTrue(failure.isPresent());
    }

    @Test
    public void testVerifyFailsWithManipulatedPublicKey() {
        publicKeyBytes[publicKeyBytes.length / 2]++;
        Optional<Failure> failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);

        Assert.assertTrue(failure.isPresent());
    }

    @Test
    public void testVerifyFailsWithWrongContent() {
        contentBytes[contentBytes.length / 2]++;
        Optional<Failure> failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);

        Assert.assertTrue(failure.isPresent());
    }
}

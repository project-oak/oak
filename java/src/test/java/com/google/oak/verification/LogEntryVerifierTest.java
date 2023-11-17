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

package com.google.oak.verification;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class LogEntryVerifierTest {
  private static final String LOG_ENTRY_PATH =
      "oak_attestation_verification/testdata/logentry.json";
  private static final String REKOR_PUBLIC_KEY_PATH =
      "oak_attestation_verification/testdata/rekor_public_key.pem";
  private static final String ENDORSEMENT_PATH =
      "oak_attestation_verification/testdata/endorsement.json";

  private RekorLogEntry logEntry;
  private byte[] publicKeyBytes;
  private byte[] endorsementBytes;

  @Before
  public void setUp() throws Exception {
    byte[] logEntryBytes = Files.readAllBytes(Path.of(LOG_ENTRY_PATH));
    logEntry = RekorLogEntry.createFromJson(logEntryBytes);
    publicKeyBytes =
        SignatureVerifier.convertPemToRaw(Files.readString(Path.of(REKOR_PUBLIC_KEY_PATH)));
    endorsementBytes = Files.readAllBytes(Path.of(ENDORSEMENT_PATH));
  }

  @Test
  public void testVerifySucceeds() {
    Optional<Failure> failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes);

    Assert.assertFalse(failure.isPresent());
  }

  @Test
  public void testVerifyFailsWithManipulatedLogEntry() {
    logEntry.logEntry.logIndex++;
    Optional<Failure> failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes);

    Assert.assertTrue(failure.isPresent());
  }

  @Test
  public void testVerifyFailsWithManipulatedPublicKey() {
    publicKeyBytes[publicKeyBytes.length / 2]++;
    Optional<Failure> failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes);

    Assert.assertTrue(failure.isPresent());
  }

  @Test
  public void testVerifyFailsWithManipulatedEndorsement() {
    endorsementBytes[endorsementBytes.length / 2]++;
    Optional<Failure> failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes);

    Assert.assertTrue(failure.isPresent());
  }
}

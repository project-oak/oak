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

import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.ReferenceValues;
import java.lang.ref.Reference;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class MainVerifierTest {
  private static final String LOG_ENTRY_PATH = "oak_remote_attestation_verification/testdata/logentry.json";
  private static final String PUBLIC_KEY_PATH = "oak_remote_attestation_verification/testdata/oak-development.pem";
  private static final String CONTENT_PATH = "oak_remote_attestation_verification/testdata/endorsement.json";

  private byte[] logEntryBytes;
  private byte[] publicKeyBytes;
  private byte[] contentBytes;

  @Before
  public void setUp() throws Exception {
    logEntryBytes = Files.readAllBytes(Path.of(LOG_ENTRY_PATH));
    publicKeyBytes = SignatureVerifier.convertPemToRaw(Files.readString(Path.of(PUBLIC_KEY_PATH)));
    contentBytes = Files.readAllBytes(Path.of(CONTENT_PATH));
  }

  @Test
  public void testVerifySucceeds() {
    Evidence evidence = Evidence.newBuilder().build();
    Endorsements endorsements = Endorsements.newBuilder().build();
    ReferenceValues referenceValues = ReferenceValues.newBuilder().build();

    MainVerifier verifier = new MainVerifier(evidence, endorsements);
    Optional<Failure> failure = verifier.verify(referenceValues);

    Assert.assertFalse(failure.isPresent());
  }
}

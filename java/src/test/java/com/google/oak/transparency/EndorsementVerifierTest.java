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

import com.google.oak.util.Result;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class EndorsementVerifierTest {
  @Test
  public void testVerifyRekorLogEntry() throws Exception {
    String logEntryPath = "oak_remote_attestation_verification/testdata/logentry.json";
    String endorsementPath = "oak_remote_attestation_verification/testdata/endorsement.json";
    String rekorPubkeyPath = "oak_remote_attestation_verification/testdata/rekor_public_key.pem";

    byte[] logEntryBytes = Files.readAllBytes(Path.of(logEntryPath));
    byte[] endorsementBytes = Files.readAllBytes(Path.of(endorsementPath));
    byte[] rekorPublicKeyBytes = Files.readAllBytes(Path.of(rekorPubkeyPath));
    Result<Boolean, Exception> result = new EndorsementVerifier().verifyRekorLogEntry(
        logEntryBytes, rekorPublicKeyBytes, endorsementBytes);
    Assert.assertTrue(result.isSuccess());
  }
}

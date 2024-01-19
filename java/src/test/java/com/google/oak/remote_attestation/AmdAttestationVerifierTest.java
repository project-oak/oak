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

package com.google.oak.remote_attestation;

import com.google.oak.attestation.v1.AttestationResults;
import com.google.oak.remote_attestation.AmdAttestationVerifier;
import com.google.oak.util.Result;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class AmdAttestationVerifierTest {
  // TODO(#3641): Add reference value implementation.
  private static final byte[] TEST_REFERENCE_VALUE = new byte[0];

  @Test
  public void testVerify() throws Exception {
    // TODO(#3641): Implement AMD SEV-SNP attestation verification.
    AmdAttestationVerifier verifier = new AmdAttestationVerifier(TEST_REFERENCE_VALUE);
    Result<AttestationResults, Exception> verifyResult = verifier.verify(0, null, null, null);
    Assert.assertTrue(verifyResult.isSuccess());
  }
}

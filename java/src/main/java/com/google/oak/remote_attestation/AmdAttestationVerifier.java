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
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.util.Result;

/**
 * Attestation verifier implementation for AMD SEV-SNP.
 * <https://www.amd.com/system/files/TechDocs/SEV-SNP-strengthening-vm-isolation-with-integrity-protection-and-more.pdf>
 */
public class AmdAttestationVerifier implements AttestationVerifier {
  // TODO(#3641): Add reference value implementation.
  private final byte[] referenceValue;

  /**
   * Creates an instance of {@code com.google.oak.remote_attestation.AmdAttestationVerifier}.
   *
   * @param referenceValue contains values used to verify the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
   */
  public AmdAttestationVerifier(byte[] referenceValue) {
    this.referenceValue = referenceValue;
  }

  /**
   * Verify that the provided evidence was endorsed and contains specified reference values.
   *
   * @param evidence contains claims about the Trusted Execution Environment
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-evidence>
   * @param endorsement contains statements that the endorsers vouch for the integrity of claims
   * provided in the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-endorsements>
   * @return boolean corresponding to the sussess of the verification wrapped in a {@code Result}
   */
  // TODO(#3641): Rewrite java-doc to represent actual AMD attestation verification.
  @Override
  public final Result<AttestationResults, Exception> verify(long nowUtcMillis,
      final Evidence evidence, final Endorsements endorsements,
      final ReferenceValues referenceValues) {
    // TODO(#3641): Implement AMD SEV-SNP attestation verification.
    if (referenceValue.length == 0) {
      return Result.success(AttestationResults.getDefaultInstance());
    } else {
      return Result.error(new Exception("unsupported reference value"));
    }
  }
}

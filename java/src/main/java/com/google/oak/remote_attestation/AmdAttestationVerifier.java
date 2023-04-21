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

import com.google.oak.util.Result;
import oak.session.noninteractive.v1.AttestationEndorsement;
import oak.session.noninteractive.v1.AttestationEvidence;

/**
 * Attestation verifier implementation for AMD SEV-SNP.
 * <https://www.amd.com/system/files/TechDocs/SEV-SNP-strengthening-vm-isolation-with-integrity-protection-and-more.pdf>
 */
public class AmdAttestationVerifier implements AttestationVerifier {
  // TODO(#3641): Add reference value implementation.
  private final byte[] reference_value;

  /**
   * Creates an instance of {@code com.google.oak.remote_attestation.AmdAttestationVerifier}.
   * 
   * @param reference_value contains values used to verify the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
   */
  public AmdAttestationVerifier(byte[] reference_value) {
    this.reference_value = reference_value;
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
  public final Result<Boolean, Exception> verify(final AttestationEvidence evidence,
      final AttestationEndorsement endorsement) {
    // TODO(#3641): Implement AMD SEV-SNP attestation verification.
    return Result.success(true);
  }
}

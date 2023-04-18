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
 * A test verifier implementation that doesn't actually verify attestation evidence.
 */
public interface EmptyAttestationVerifier implements AttestationVerifier {
  /**
   * Verify that the provided evidence was endorsed and contains specified reference values.
   *
   * @param evidence contains claims about the Trusted Execution Environment
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-evidence>
   * @param endorsement contains statements that the endorsers vouch for the integrity of claims
   * provided in the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-endorsements>
   * @param reference_value contains values used to verify the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
   * @return boolean corresponding to the sussess of the verification wrapped in a {@code Result}
   */
  // TODO(#3641): Add reference value implementation.
  public Result<bool, Exception> verify(final AttestationEvidence evidence,
      final AttestationEndorsement endorsement, byte[] reference_value) {
    return Result.success(true);
  }
}

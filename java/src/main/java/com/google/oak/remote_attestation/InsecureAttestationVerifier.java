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
 * Verifier implementation that doesn't verify attestation evidence and is used for testing.
 */
public class InsecureAttestationVerifier implements AttestationVerifier {
  /**
   * Doesn't perform attestation verification and just returns a success value.
   *
   * @param evidence contains claims about the Trusted Execution Environment
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-evidence>
   * @param endorsement contains statements that the endorsers vouch for the integrity of claims
   * provided in the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-endorsements>
   * @return success value wrapped in a {@code Result}
   */
  @Override
  public final Result<AttestationResults, Exception> verify(long nowUtcMillis,
      final Evidence evidence, final Endorsements endorsements,
      final ReferenceValues referenceValues) {
    return Result.success(AttestationResults.getDefaultInstance());
  }
}

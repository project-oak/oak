//
// Copyright 2022 The Project Oak Authors
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

package com.google.oak.evidence;

import com.google.oak.util.Result;

/**
 * Endorsement evidence about a trusted Oak runtime. This class contains five fields:
 *
 * <p><ul>
 * <li>The endorsement statement,
 * <li>The signature over the endorsement; (what is the signature exactly in the case of in-toto
 * attestation?),
 * <li>The log entry from Rekor as a proof of inclusion of the endorsement in Rekor,
 * <li>Public key of Rekor, likely loaded from a static file,
 * <li>Public key of the product team (in this case Oak), likely loaded from a static file.
 * </ul><p>
 */
public class EndorsementEvidence implements Evidence {
  // TODO(#2854): We probably need a Factory class for generating EndorsementEvidence from an
  // in-toto attestation with attached signature.

  /**
   * Verifies this endorsement evidence and returns the SHA256 hash of the subject of this
   * endorsement if the verification succeeds. Otherwise returns a result containing an error.
   *
   * @return SHA256 hash of the subject, or an error if the verification fails
   */
  Result<byte[], Exception> verify() {
    // TODO(#2854): Implement this method.
    return Result.success(new byte[] {});
  }
}

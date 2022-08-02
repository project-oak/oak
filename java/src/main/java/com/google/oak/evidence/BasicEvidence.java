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

import com.google.oak.evidence.AttestationReport;
import com.google.oak.evidence.EndorsementEvidence;
import com.google.oak.evidence.Evidence;
import com.google.oak.util.Result;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.StackWalker.Option;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Function;

/**
 * This class encapsulates the logic for verifying minimal evidence about server's identity. It
 * verifies an attestation report, from which the public key of the server's signing key can be
 * retrieved. It also verifies the provided endorsement evidence. The verification is successful
 * only if the hash of the binary in the attestation report matches the hash of the binary in the
 * endorsement evidence. The user of this class can register additional verifiers for verifying the
 * attestation report.
 *
 * @param A type of the {@code AttestationReport}
 */
public class BasicEvidence<A extends AttestationReport> implements Evidence {
  private final A attestationReport;
  private final EndorsementEvidence endorsement;

  public BasicEvidence(A attestationReport, EndorsementEvidence endorsement) {
    this.attestationReport = attestationReport;
    this.endorsement = endorsement;
  }

  /**
   * Verifies this evidence. If the verification is successful, returns the public key of the
   * server's signing key. Otherwise, returns an error.
   *
   * @return the public key of the server's signing key, or error if verification fails
   */
  public Result<byte[], Exception> verify() {
    return attestationReport.verify().andThen(publicKey
        -> endorsement.verify().andThen(binaryHash
            -> attestationReport.getServerBinarySha256Hash().andThen(attestedBinaryHash -> {
      if (Arrays.equals(binaryHash, attestedBinaryHash)) {
        return Result.success(publicKey);
      }
      return Result.error(
          new Exception("evidence verification failed, binary hashes do not match"));
    })));
  }

  public String exceptionToString(Exception exception) {
    StringWriter sw = new StringWriter();
    exception.printStackTrace(new PrintWriter(sw));
    return sw.toString();
  }
}

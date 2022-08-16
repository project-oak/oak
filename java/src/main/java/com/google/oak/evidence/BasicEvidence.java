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

import com.google.common.hash.Hashing;
import com.google.oak.evidence.AttestationReport;
import com.google.oak.evidence.EndorsementEvidence;
import com.google.oak.evidence.Evidence;
import com.google.oak.util.Result;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.StackWalker.Option;
import java.security.PublicKey;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Function;

/**
 * This class encapsulates the logic for verifying minimal evidence about server's identity (i.e.,
 * its public key). It verifies an attestation report, from which the SHA256 hash of the public key
 * of the server's signing key can be retrieved. It also verifies the endorsement evidence about the
 * server binary. The verification is successful only if the hash of the binary in the attestation
 * report matches the hash of the binary in the endorsement evidence.
 *
 * @param A type of the {@code AttestationReport}
 */
public class BasicEvidence<A extends AttestationReport> implements Evidence {
  private final A attestationReport;
  private final EndorsementEvidence endorsement;
  private final PublicKeyInfo publicKeyInfo;

  public static class PublicKeyInfo {
    private final byte[] publicKey;

    public PublicKeyInfo(final byte[] publicKey) {
      this.publicKey = publicKey;
    }

    byte[] getPublicKeySha256Hash() {
      return Hashing.sha256().hashBytes(publicKey).asBytes();
    }
  }

  public BasicEvidence(
      A attestationReport, EndorsementEvidence endorsement, final byte[] publicKey) {
    this.attestationReport = attestationReport;
    this.endorsement = endorsement;
    this.publicKeyInfo = new PublicKeyInfo(publicKey);
  }

  /**
   * Verifies this evidence. If the verification is successful, returns the public key of the
   * server's signing key. Otherwise, returns an error.
   *
   * @return the public key of the server's signing key, or error if verification fails
   */
  public Result<byte[], Exception> verify() {
    return attestationReport.verify().andThen(publicKeyHash
        -> endorsement.verify().andThen(binaryHash
            -> attestationReport.getServerBinarySha256Hash().andThen(attestedBinaryHash -> {
      if (Arrays.equals(binaryHash, attestedBinaryHash)
          && Arrays.equals(publicKeyHash, publicKeyInfo.getPublicKeySha256Hash())) {
        return Result.success(publicKeyInfo.publicKey);
      }
      return Result.error(
          new Exception("evidence verification failed, binary hashes do not match"));
    })));
  }
}

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
import com.google.oak.util.Result;

// TODO(#2842): This is a placeholder implementation, and must be replaced with a valid and
// complete implementation.
/**
 * Placeholder implementation of the remote attestation report from AMD SEV-SNP.
 */
public class AmdAttestationReport implements AttestationReport {
  // TODO(#2842): In a valid implementation, it should be extracted from the report.
  private final byte[] publicKeyHash;

  // TODO(#2842): In a valid implementation, it should be extracted from the report.
  private final byte[] binaryHash;

  @Override
  public Result<byte[], Exception> getServerSigningPublicKeySha256Hash() {
    return Result.success(publicKeyHash.clone());
  }

  @Override
  public Result<byte[], Exception> getServerBinarySha256Hash() {
    return Result.success(binaryHash.clone());
  }

  @Override
  public Result<byte[], Exception> verify() {
    // TODO(#2842): Implement the verification logic.
    return getServerSigningPublicKeySha256Hash();
  }

  // TODO(#2842): Remove once we have a valid implementation.
  /**
   * Creates a placeholder instance of {@code AmdAttestationReport}, with the given {@code
   * publicKeyHash} and {@code binaryHash}. This is suitable for testing, and will be removed when
   * we have a complete and valid implementation of the AMD Attestation report.
   */
  public static AmdAttestationReport createPlaceholder(
      final byte[] publicKeyHash, final byte[] binaryHash) {
    return new AmdAttestationReport(publicKeyHash, binaryHash);
  }

  // This is a placeholder constructor and is therefore private.
  // TODO(#2842): Remove once we have a valid implementation.
  private AmdAttestationReport(final byte[] publicKeyHash, final byte[] binaryHash) {
    this.publicKeyHash = publicKeyHash;
    this.binaryHash = binaryHash;
  }
}

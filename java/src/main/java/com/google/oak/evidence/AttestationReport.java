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
 * Interface representing an attestation report. Different implementations of this interface are
 * required for each Trusted Execution Environment (TEE) architecture (e.g., AMD).
 */
public interface AttestationReport extends Evidence {
  /**
   * Extracts and returns the public key part of the server's signing key included in this
   * attestation report. The client code is responsible for verifying this report before trusting
   * the public key.
   *
   * @return public key part of the remote server's signing key
   */
  Result<byte[], Exception> getServerSigningPublicKey();

  /**
   * Extracts and returns the SHA256 hash of the remote server's binary. The client code is
   * responsible for verifying this report before trusting returned hash.
   *
   * @return SHA256 hash of the trusted runtime binary running on the server
   */
  Result<byte[], Exception> getServerBinarySha256Hash();

  /**
   * Verifies this attestation report. Returns {@code getServerSigningPublicKey()} if the
   * verification is successful, otherwise returns an error indicating that the verification failed.
   */
  Result<byte[], Exception> verify();
}

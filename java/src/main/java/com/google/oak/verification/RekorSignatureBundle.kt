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
package com.google.oak.verification

/**
 * Convenient struct for verifying the `signedEntryTimestamp` in a Rekor LogEntry.
 *
 * This bundle can be verified using the public key from Rekor. The public key can be obtained from
 * the /api/v1/log/publicKey Rest API. For [sigstore.dev], it is a PEM-encoded x509/PKIX public key.
 */
data class RekorSignatureBundle(
  /**
   * Canonicalized JSON representation, based on RFC 8785 rules, of a subset of a Rekor LogEntry
   * fields that are signed to generate `signedEntryTimestamp` (also a field in the Rekor LogEntry).
   * These fields include body, integratedTime, logID and logIndex.
   */
  val canonicalized: String,
  /** Base64-encoded signature over the canonicalized JSON document. */
  val base64Signature: String,
) {
  companion object {
    const val TEMPLATE = "{\"body\":\"%s\",\"integratedTime\":%d,\"logID\":\"%s\",\"logIndex\":%d}"

    /** Creates a bundle from the given log entry. */
    fun create(logEntry: RekorLogEntry): RekorSignatureBundle {
      val e = logEntry.logEntry
      val canonicalized = TEMPLATE.format(e.body, e.integratedTime, e.logID, e.logIndex)
      return RekorSignatureBundle(canonicalized, e.verification!!.signedEntryTimestamp)
    }
  }
}

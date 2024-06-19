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

import java.io.File
import org.junit.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class LogEntryVerifierTest {
  private val logEntryBytes = File(LOG_ENTRY_PATH).readBytes()
  private val logEntry = RekorLogEntry.createFromJson(logEntryBytes)
  private val publicKeyBytes = SignatureVerifier.convertPemToRaw(
      File(REKOR_PUBLIC_KEY_PATH).readText()
    )
  private val endorsementBytes = File(ENDORSEMENT_PATH).readBytes()

  @Test
  fun testVerifySucceeds() {
    val failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes)
    assertFalse(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithManipulatedLogEntry() {
    logEntry.logEntry.logIndex++
    val failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes)
    assertTrue(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithManipulatedPublicKey() {
    publicKeyBytes[publicKeyBytes.size / 2]++
    val failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes)
    assertTrue(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithManipulatedEndorsement() {
    endorsementBytes[endorsementBytes.size / 2]++
    val failure = LogEntryVerifier.verify(logEntry, publicKeyBytes, endorsementBytes)
    assertTrue(failure.isPresent())
  }

  companion object {
    private const val LOG_ENTRY_PATH = "oak_attestation_verification/testdata/logentry.json"
    private const val REKOR_PUBLIC_KEY_PATH =
      "oak_attestation_verification/testdata/rekor_public_key.pem"
    private const val ENDORSEMENT_PATH = "oak_attestation_verification/testdata/endorsement.json"
  }
}

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
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import org.junit.Test

class SignatureVerifierTest {
  private val signatureBytes = File(SIGNATURE_PATH).readBytes()
  private val publicKeyBytes = SignatureVerifier.convertPemToRaw(File(PUBLIC_KEY_PATH).readText())
  private val contentBytes = File(CONTENT_PATH).readBytes()

  @Test
  fun testVerifySucceeds() {
    val failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
    assertFalse(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithManipulatedSignature() {
    signatureBytes[signatureBytes.size / 2]++
    val failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
    assertTrue(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithManipulatedPublicKey() {
    publicKeyBytes[publicKeyBytes.size / 2]++
    val failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
    assertTrue(failure.isPresent())
  }

  @Test
  fun testVerifyFailsWithWrongContent() {
    contentBytes[contentBytes.size / 2]++
    val failure = SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
    assertTrue(failure.isPresent())
  }

  companion object {
    private const val SIGNATURE_PATH = "oak_attestation_verification/testdata/endorsement.json.sig"
    private const val PUBLIC_KEY_PATH =
      "oak_attestation_verification/testdata/oak_containers_stage1.pem"
    private const val CONTENT_PATH = "oak_attestation_verification/testdata/endorsement.json"
  }
}

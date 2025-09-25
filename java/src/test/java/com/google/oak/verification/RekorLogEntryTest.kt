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
package com.google.oak.verification

import java.io.File
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import org.junit.Test

class RekorLogEntryTest {
  @Test
  @kotlin.Throws(Exception::class)
  fun testCreate() {
    val json: String = File(LOG_ENTRY_PATH).readText()
    val r = RekorLogEntry.createFromJson(json)
    assertTrue(r.hasVerification())
    assertTrue(r.logEntry.body.isNotEmpty() == true)
    assertEquals(132193865, r.logEntry.logIndex)
    assertEquals("rekord", r.logEntry.bodyObject?.kind)
    assertEquals("sha256", r.logEntry.bodyObject?.spec?.data?.hash?.algorithm)
  }

  companion object {
    private const val LOG_ENTRY_PATH = "oak_attestation_verification/testdata/logentry.json"
  }
}

/*
 * Copyright 2026 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.oak.util

import java.io.File
import java.io.IOException
import java.nio.charset.StandardCharsets
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

@RunWith(JUnit4::class)
class FileUtilTest {
  companion object {
    private const val TEST_FILE = "oak_session/tls/testing/test_ca.pem"
  }

  @Test
  fun testGetRunfilePath() {
    val path = FileUtil.getRunfilePath(TEST_FILE)
    assertNotNull(path)
    val file = File(path)
    assertTrue(file.exists(), "File should exist: $path")
    assertTrue(file.isAbsolute, "File should be absolute: $path")
  }

  @Test
  @Throws(IOException::class)
  fun testGetRunfileBytes() {
    val bytes = FileUtil.getRunfileBytes(TEST_FILE)
    assertNotNull(bytes)
    assertTrue(bytes.isNotEmpty())
    val content = String(bytes, StandardCharsets.UTF_8)
    assertTrue(content.contains("BEGIN CERTIFICATE"))
  }
}

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

import com.google.devtools.build.runfiles.Runfiles
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Paths

/** Helper for loading Bazel/Blaze data dependencies. */
object FileUtil {
  // Prefix prepended to all data dependency file paths.
  // This defaults to "oak/" in this repository, but can be transformed by import tools
  // to point the appropriate subfolder when importing this code into other repositories.
  private const val DATA_FILE_PREFIX = "oak/"

  @Suppress("DEPRECATION") private val runfiles: Runfiles by lazy { Runfiles.create() }

  /**
   * Resolves a path to a data dependency (runfile).
   *
   * @param path the workspace-relative path (e.g. "oak_session/tls/testing/test_server.key")
   * @return the resolved absolute path as a String
   */
  @JvmStatic
  fun getRunfilePath(path: String): String {
    val prefixedPath = "$DATA_FILE_PREFIX$path"
    val r = runfiles
    return r.rlocation(prefixedPath) ?: prefixedPath
  }

  /**
   * Loads the bytes of a data dependency.
   *
   * @param path the workspace-relative path
   * @return the bytes of the file
   * @throws IOException if the file cannot be read
   */
  @JvmStatic
  @Throws(IOException::class)
  fun getRunfileBytes(path: String): ByteArray {
    return Files.readAllBytes(Paths.get(getRunfilePath(path)))
  }
}

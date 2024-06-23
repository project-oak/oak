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
import java.nio.charset.StandardCharsets
import java.security.KeyFactory
import java.security.PublicKey
import java.security.Signature
import java.security.spec.X509EncodedKeySpec
import java.util.Base64
import java.util.Optional
import java.util.logging.Logger

/** Verifies a signature based on a public key. */
object SignatureVerifier {
  /**
   * Needs three paths as command line arguments, corresponding to the arguments of `#verify()`.
   * Verification failure is signalled via exit code.
   */
  @JvmStatic
  fun main(args: Array<String?>) {
    if (args.size != 3) {
      System.exit(2)
    }
    val signatureBytes = File(args[0]!!).readBytes()
    var publicKeyBytes = File(args[1]!!).readBytes()
    val contentBytes = File(args[2]!!).readBytes()

    // Auto-detect PEM format of public key.
    val publicKeyString = String(publicKeyBytes, StandardCharsets.UTF_8)
    if (looksLikePem(publicKeyString)) {
      publicKeyBytes = convertPemToRaw(publicKeyString)
    }
    val failure: Optional<Failure> = verify(signatureBytes, publicKeyBytes, contentBytes)
    if (failure.isPresent()) {
      logger.warning("Verification failed: ${failure.get().message}")
      System.exit(1)
    }
  }

  private val logger: Logger = Logger.getLogger(SignatureVerifier::class.java.getName())

  private fun failure(message: String) = Optional.of(Failure(message))

  /**
   * Verifies the signature over content bytes using a public key.
   *
   * @param signatureBytes the raw ECDSA signature, likely 71 bytes long
   * @param publicKeyBytes the raw public key
   * @param contentBytes the serialized content
   * @return empty if the verification succeeds, or a failure otherwise
   */
  fun verify(
      signatureBytes: ByteArray,
      publicKeyBytes: ByteArray,
      contentBytes: ByteArray
  ): Optional<Failure> {
    if (signatureBytes.isEmpty()) {
      return failure("empty signature")
    }
    if (publicKeyBytes.isEmpty()) {
      return failure("empty public key")
    }
    if (contentBytes.isEmpty()) {
      return failure("empty content")
    }
    val keySpec = X509EncodedKeySpec(publicKeyBytes)
    return try {
      val keyFactory = KeyFactory.getInstance("EC")
      val publicKey: PublicKey = keyFactory.generatePublic(keySpec)
      val s = Signature.getInstance("SHA256withECDSA")
      s.initVerify(publicKey)
      s.update(contentBytes)
      if (s.verify(signatureBytes)) {
        Optional.empty()
      } else {
        failure("verification failed")
      }
    } catch (e: Exception) {
      failure("$e")
    }
  }

  private const val PEM_HEADER = "-----BEGIN PUBLIC KEY-----"
  private const val PEM_FOOTER = "-----END PUBLIC KEY-----"

  /** Makes a plausible guess whether the public key is in PEM format. */
  fun looksLikePem(maybePem: String): Boolean =
      maybePem.trim().run { startsWith(PEM_HEADER) && endsWith(PEM_FOOTER) }

  /** Converts a public key from PEM (on disk format) to raw binary format. */
  fun convertPemToRaw(pem: String): ByteArray {
    val trimmed: String =
        pem.replace(PEM_HEADER, "").replace(PEM_FOOTER, "").replace("\n", "").trim()
    return Base64.getDecoder().decode(trimmed)
  }
}

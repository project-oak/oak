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
import java.security.MessageDigest
import java.security.NoSuchAlgorithmException
import java.util.Base64
import java.util.Optional
import java.util.logging.Level
import java.util.logging.Logger

/** Verifies a Rekor log entry against an endorsement statement. */
object LogEntryVerifier {
  /**
   * Needs three paths as command line arguments, corresponding to the arguments of `#verify()`.
   * Verification failure is signalled via exit code.
   */
  @JvmStatic
  fun main(args: Array<String?>) {
    if (args.size != 3) {
      System.exit(2)
    }
    val logEntryBytes = File(args[0]!!).readBytes()
    var publicKeyBytes = File(args[1]!!).readBytes()
    val endorsementBytes = File(args[2]!!).readBytes()

    // Auto-detect PEM format of public key.
    val publicKeyString = String(publicKeyBytes, StandardCharsets.UTF_8)
    if (SignatureVerifier.looksLikePem(publicKeyString)) {
      publicKeyBytes = SignatureVerifier.convertPemToRaw(publicKeyString)
    }
    val logEntry: RekorLogEntry = RekorLogEntry.createFromJson(logEntryBytes)
    val failure: Optional<Failure> = verify(logEntry, publicKeyBytes, endorsementBytes)
    if (failure.isPresent()) {
      logger.warning("Verification failed: ${failure.get().message}")
      System.exit(1)
    }
  }

  private val logger: Logger = Logger.getLogger(LogEntryVerifier::class.java.getName())

  private fun failure(message: String) = Optional.of(Failure(message))

  /**
   * Verifies a Rekor log entry.
   *
   * Verifies the signature of `logEntry.verification.signedEntryTimestamp` using the provided
   * public key, the signature in `logEntry.body.RekordObj.signature` using the endorser's public
   * key `logEntry.body.spec.signature.publicKey`, as well as digest equality of
   * `logEntry.body.spec.data.hash` and the endorsement statement.
   *
   * @param logEntry the Rekor log entry
   * @param publicKeyBytes the raw public key from Rekor
   * @param endorsementBytes the serialized endorsement statement
   * @return empty if the verification succeeds, or a failure otherwise
   */
  fun verify(
    logEntry: RekorLogEntry,
    publicKeyBytes: ByteArray,
    endorsementBytes: ByteArray,
  ): Optional<Failure> {
    val rekorSigVer = verifyRekorSignature(logEntry, publicKeyBytes)
    return if (rekorSigVer.isPresent()) {
      rekorSigVer
    } else verifyRekorBody(logEntry.body!!, endorsementBytes)
  }

  /**
   * Verifies the Rekor signature of a log entry using a public key.
   *
   * @param logEntry the Rekor log entry
   * @param publicKeyBytes the raw public key
   * @return empty if the verification succeeds, or a failure otherwise
   */
  fun verifyRekorSignature(logEntry: RekorLogEntry, publicKeyBytes: ByteArray): Optional<Failure> {
    if (!logEntry.hasVerification()) {
      return failure("no verification in the log entry")
    }
    val bundle = RekorSignatureBundle.create(logEntry)
    val signatureBytes = Base64.getDecoder().decode(bundle.base64Signature)
    val contentBytes = bundle.canonicalized.toByteArray(StandardCharsets.UTF_8)
    return SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
  }

  /**
   * Verifies the integrity of the Rekor body, by verifying the signature in the `body` over the
   * given `contentBytes`, using the public key in the `body`.
   *
   * @param body the body of the Rekor log entry
   * @param contentBytes the serialized content
   * @return empty if the verification succeeds, or a failure otherwise
   */
  fun verifyRekorBody(body: RekorLogEntry.Body, contentBytes: ByteArray): Optional<Failure> {
    if (body.kind != "rekord" && body.kind != "hashedrekord") {
      return failure("unsupported Rekor type: ${body.kind}")
    }

    // For now, we only support `sha256` as the hashing algorithm.
    if (body.spec.data.hash.algorithm != "sha256") {
      return failure(
        "unsupported hash algorithm: ${body.spec.data.hash.algorithm} only sha256 is supported"
      )
    }

    // Content digest must match the hash mentioned in the body.
    val digest = sha256Hex(contentBytes)
    if (body.spec.data.hash.value != digest) {
      return failure(
        "SHA2-256 digest of contents ($digest) differs from that in Rekor entry body (${body.spec.data.hash.value})"
      )
    }
    val signatureBytes = Base64.getDecoder().decode(body.spec.signature.content)
    val publicKeyBytes =
      SignatureVerifier.convertPemToRaw(
        Base64.getDecoder()
          .decode(body.spec.signature.publicKey.content)
          .toString(StandardCharsets.UTF_8)
      )
    return SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes)
  }

  /**
   * Computes the hex-encoded SHA2-256 digest.
   *
   * @param bytes the binary content to compute the digest from
   * @return the hex-encoded SHA2-256 digest of `bytes`
   */
  fun sha256Hex(bytes: ByteArray): String? {
    return try {
      val md: MessageDigest = MessageDigest.getInstance("SHA-256")
      val digest: ByteArray = md.digest(bytes)
      val result = StringBuilder()
      for (b in digest) {
        result.append(String.format("%02x", b))
      }
      result.toString()
    } catch (e: NoSuchAlgorithmException) {
      logger.log(Level.SEVERE, e.message)
      null
    }
  }
}

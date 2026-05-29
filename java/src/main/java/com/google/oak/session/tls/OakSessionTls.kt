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

package com.google.oak.session.tls

import java.nio.ByteBuffer
import javax.net.ssl.SSLEngine
import javax.net.ssl.SSLEngineResult
import javax.net.ssl.SSLException

/**
 * Represents an open Oak Session (TLS) that can be used to encrypt and decrypt.
 *
 * Cannot be constructed directly. Instead, obtain an initialized instance by completing a handshake
 * using [OakSessionTlsInitializer] or [OakSessionTlsContext.newInitializedSession].
 *
 * This class wraps a completed [SSLEngine] and uses `wrap()`/`unwrap()` for encrypt/decrypt,
 * operating entirely on byte arrays without network sockets. This is the Kotlin equivalent of the
 * C++ `OakSessionTls` which uses BoringSSL's memory BIOs.
 */
class OakSessionTls internal constructor(private val engine: SSLEngine) {

  companion object {
    private const val MAX_TLS_FRAME_SIZE = 16 * 1024 + 256 // 16KB + overhead
  }

  /**
   * Encrypts the plaintext message into the caller-provided buffer (or a newly allocated one if
   * capacity is insufficient or buffer is null) and returns it.
   *
   * After completion, the returned buffer is flipped and ready to be read from.
   *
   * @param plaintext the application-level plaintext message
   * @param outBuffer optional pre-allocated buffer to use as intermediate/destination space to
   *   avoid allocation churn
   * @return the ByteBuffer containing the TLS-encrypted frame (either outBuffer or a new one)
   * @throws OakSessionTlsException if encryption fails
   */
  @JvmOverloads
  @Throws(OakSessionTlsException::class)
  fun encrypt(plaintext: ByteArray, outBuffer: ByteBuffer? = null): ByteBuffer {
    try {
      val input = ByteBuffer.wrap(plaintext)
      val packetSize = engine.session.packetBufferSize
      val estimatedRecords = (plaintext.size / (packetSize - 256)) + 2
      val requiredCapacity = estimatedRecords * packetSize

      var output: ByteBuffer =
        if (outBuffer != null && outBuffer.capacity() >= requiredCapacity) {
          outBuffer
        } else {
          ByteBuffer.allocate(requiredCapacity)
        }
      output.clear()

      while (input.hasRemaining()) {
        val result = engine.wrap(input, output)
        when (result.status!!) {
          SSLEngineResult.Status.OK -> {}
          SSLEngineResult.Status.BUFFER_OVERFLOW -> {
            val expanded = ByteBuffer.allocate(output.capacity() + packetSize + MAX_TLS_FRAME_SIZE)
            output.flip()
            expanded.put(output)
            output = expanded
          }
          SSLEngineResult.Status.CLOSED -> throw OakSessionTlsException("SSL engine is closed")
          SSLEngineResult.Status.BUFFER_UNDERFLOW ->
            throw OakSessionTlsException("unexpected BUFFER_UNDERFLOW during wrap")
        }
      }

      output.flip()
      return output
    } catch (e: SSLException) {
      throw OakSessionTlsException("encryption failed", e)
    }
  }

  /**
   * Decrypts the TLS frame into the caller-provided buffer (or a newly allocated one if capacity is
   * insufficient or buffer is null) and returns it.
   *
   * After completion, the returned buffer is flipped and ready to be read from.
   *
   * @param tlsFrame the TLS-encrypted frame
   * @param outBuffer optional pre-allocated buffer to use as intermediate/destination space to
   *   avoid allocation churn
   * @return the ByteBuffer containing the decrypted plaintext (either outBuffer or a new one)
   * @throws OakSessionTlsException if decryption fails
   */
  @JvmOverloads
  @Throws(OakSessionTlsException::class)
  fun decrypt(tlsFrame: ByteArray, outBuffer: ByteBuffer? = null): ByteBuffer {
    try {
      val input = ByteBuffer.wrap(tlsFrame)
      val appSize = engine.session.applicationBufferSize
      val requiredCapacity = maxOf(tlsFrame.size, appSize + MAX_TLS_FRAME_SIZE)

      var output: ByteBuffer =
        if (outBuffer != null && outBuffer.capacity() >= requiredCapacity) {
          outBuffer
        } else {
          ByteBuffer.allocate(requiredCapacity)
        }
      output.clear()

      while (input.hasRemaining()) {
        val result = engine.unwrap(input, output)
        when (result.status!!) {
          SSLEngineResult.Status.OK -> {}
          SSLEngineResult.Status.BUFFER_OVERFLOW -> {
            val expanded = ByteBuffer.allocate(output.capacity() + appSize + MAX_TLS_FRAME_SIZE)
            output.flip()
            expanded.put(output)
            output = expanded
          }
          SSLEngineResult.Status.BUFFER_UNDERFLOW ->
            throw OakSessionTlsException("incomplete TLS record in decrypt")
          SSLEngineResult.Status.CLOSED -> throw OakSessionTlsException("SSL engine is closed")
        }
      }

      output.flip()
      return output
    } catch (e: SSLException) {
      throw OakSessionTlsException("decryption failed", e)
    }
  }
}

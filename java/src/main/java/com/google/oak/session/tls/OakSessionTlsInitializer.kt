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
 * Manages the initialization state of an opening Oak TLS session.
 *
 * This class is used for manual handshake control. For most use cases, prefer
 * [OakSessionTlsContext.newInitializedSession] instead.
 *
 * Handshake flow:
 * 1. For clients: call [getTLSFrame] to get the initial ClientHello and send it
 * 2. Loop until [isReady]:
 *     - Receive data from peer and pass to [putTLSFrame]
 *     - If not ready, call [getTLSFrame] and send any response
 * 3. Call [getOpenSession] to get the initialized session
 *
 * This class wraps an [SSLEngine] operating with [ByteBuffer] I/O, equivalent to the C++
 * `OakSessionTlsInitializer` which uses BoringSSL's memory BIOs.
 */
class OakSessionTlsInitializer internal constructor(private val engine: SSLEngine) {

  /**
   * Result of a successful TLS handshake.
   *
   * Contains the initialized session ready for encrypt/decrypt operations, and any application data
   * received bundled with the final handshake message (common in TLS 1.3).
   *
   * @property session the initialized session, ready for encrypt/decrypt
   * @property initialData application data received during handshake (typically empty on client
   *   side)
   */
  class InitializedSession
  internal constructor(val session: OakSessionTls, val initialData: ByteArray = ByteArray(0))

  private var incomingNet: ByteBuffer =
    ByteBuffer.allocate(maxOf(engine.session.packetBufferSize, BUFFER_SIZE))
  private var outgoingNet: ByteBuffer =
    ByteBuffer.allocate(maxOf(engine.session.packetBufferSize, BUFFER_SIZE))
  private var appBuffer: ByteBuffer =
    ByteBuffer.allocate(maxOf(engine.session.applicationBufferSize, BUFFER_SIZE))
  private var initialData: ByteArray? = null
  private var consumed = false

  /**
   * Returns true if the handshake is complete.
   *
   * After the handshake is complete, [getOpenSession] can be used to get the open session for
   * encrypting and decrypting application data.
   */
  val isReady: Boolean
    get() {
      if (consumed) return false
      val hs = engine.handshakeStatus
      return hs == SSLEngineResult.HandshakeStatus.NOT_HANDSHAKING ||
        hs == SSLEngineResult.HandshakeStatus.FINISHED
    }

  /**
   * Put an incoming TLS frame into the initializer for processing.
   *
   * This feeds network data from the peer into the SSLEngine via `unwrap()`, advancing the
   * handshake state machine.
   *
   * @param tlsFrame the raw TLS frame bytes received from the peer
   * @throws OakSessionTlsException if the handshake was already completed or processing fails
   */
  @Throws(OakSessionTlsException::class)
  fun putTLSFrame(tlsFrame: ByteArray) {
    if (consumed) {
      throw OakSessionTlsException("initializer is no longer valid")
    }

    if (isReady && initialData != null) {
      throw OakSessionTlsException("handshake was already completed")
    }

    try {
      // Ensure incoming buffer has capacity.
      if (incomingNet.remaining() < tlsFrame.size) {
        val expanded = ByteBuffer.allocate(incomingNet.position() + tlsFrame.size)
        incomingNet.flip()
        expanded.put(incomingNet)
        incomingNet = expanded
      }
      incomingNet.put(tlsFrame)
      incomingNet.flip()

      // Process the incoming data through the SSLEngine.
      var continueProcessing = true
      while (continueProcessing && incomingNet.hasRemaining()) {
        val result = engine.unwrap(incomingNet, appBuffer)

        when (result.status!!) {
          SSLEngineResult.Status.OK -> runDelegatedTasks(engine)
          SSLEngineResult.Status.BUFFER_OVERFLOW -> {
            val expanded = ByteBuffer.allocate(appBuffer.capacity() * 2)
            appBuffer.flip()
            expanded.put(appBuffer)
            appBuffer = expanded
          }
          SSLEngineResult.Status.BUFFER_UNDERFLOW -> continueProcessing = false
          SSLEngineResult.Status.CLOSED ->
            throw OakSessionTlsException("SSL engine closed during handshake")
        }
      }

      // Compact remaining data for future reads.
      incomingNet.compact()

      // If handshake is complete, drain pending wraps and check for initial app data.
      if (isReady) {
        drainWrap(engine)

        appBuffer.flip()
        initialData =
          if (appBuffer.hasRemaining()) {
            ByteArray(appBuffer.remaining()).also { appBuffer.get(it) }
          } else {
            ByteArray(0)
          }
        appBuffer.clear()
      }
    } catch (e: SSLException) {
      throw OakSessionTlsException("TLS handshake failed", e)
    }
  }

  /**
   * Get the next outgoing TLS frame to send to the peer.
   *
   * @return the TLS frame bytes to send, or an empty array if nothing pending
   * @throws OakSessionTlsException if producing the frame fails
   */
  @Throws(OakSessionTlsException::class)
  fun getTLSFrame(): ByteArray {
    if (consumed) {
      throw OakSessionTlsException("initializer is no longer valid")
    }

    try {
      drainWrap(engine)

      outgoingNet.flip()
      if (!outgoingNet.hasRemaining()) {
        outgoingNet.clear()
        return ByteArray(0)
      }
      val result = ByteArray(outgoingNet.remaining())
      outgoingNet.get(result)
      outgoingNet.clear()
      return result
    } catch (e: SSLException) {
      throw OakSessionTlsException("failed to produce TLS frame", e)
    }
  }

  /**
   * If the handshake is complete, returns an initialized session.
   *
   * This method can only be called once. After calling this method, any subsequent calls will
   * throw.
   *
   * @return the initialized session
   * @throws OakSessionTlsException if the handshake is not complete or already consumed
   */
  @Throws(OakSessionTlsException::class)
  fun getOpenSession(): InitializedSession {
    if (!isReady) {
      throw OakSessionTlsException("handshake is not complete yet")
    }
    if (consumed) {
      throw OakSessionTlsException("getOpenSession was already called")
    }

    consumed = true
    return InitializedSession(OakSessionTls(engine), initialData ?: ByteArray(0))
  }

  /** Runs any delegated tasks queued by the SSLEngine. */
  private fun runDelegatedTasks(eng: SSLEngine) {
    var task = eng.delegatedTask
    while (task != null) {
      task.run()
      task = eng.delegatedTask
    }
  }

  /** Drains the SSLEngine's outgoing data by calling wrap() until nothing left. */
  private fun drainWrap(eng: SSLEngine) {
    var hs = eng.handshakeStatus
    while (hs == SSLEngineResult.HandshakeStatus.NEED_WRAP) {
      if (outgoingNet.remaining() < eng.session.packetBufferSize) {
        val expanded = ByteBuffer.allocate(outgoingNet.position() + BUFFER_SIZE)
        outgoingNet.flip()
        expanded.put(outgoingNet)
        outgoingNet = expanded
      }

      val result = eng.wrap(ByteBuffer.allocate(0), outgoingNet)
      runDelegatedTasks(eng)
      hs = eng.handshakeStatus

      if (result.status == SSLEngineResult.Status.CLOSED) break
    }
  }

  companion object {
    private const val BUFFER_SIZE = 32 * 1024 // 32KB
  }
}

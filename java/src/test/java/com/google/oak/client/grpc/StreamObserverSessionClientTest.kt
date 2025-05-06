//
// Copyright 2025 The Project Oak Authors
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
package com.google.oak.client.grpc

import com.google.oak.client.grpc.StreamObserverSessionClient.OakSessionStreamObserver
import com.google.oak.session.OakClientSession
import com.google.oak.session.OakServerSession
import com.google.oak.session.OakSessionConfigBuilder
import com.google.oak.session.OakSessionConfigBuilder.AttestationType
import com.google.oak.session.OakSessionConfigBuilder.HandshakeType
import com.google.oak.session.v1.PlaintextMessage
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import com.google.protobuf.ByteString
import io.grpc.stub.StreamObserver
import java.nio.charset.StandardCharsets
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import javax.inject.Provider
import kotlin.jvm.optionals.getOrNull
import org.junit.Assert.assertEquals
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4
import org.mockito.kotlin.any
import org.mockito.kotlin.argumentCaptor
import org.mockito.kotlin.mock
import org.mockito.kotlin.never
import org.mockito.kotlin.times
import org.mockito.kotlin.verify

@RunWith(JUnit4::class)
@SuppressWarnings("CheckReturnValue")
class StreamObserverSessionClientTest {
  init {
    OakServerSession.loadNativeLib()
    OakClientSession.loadNativeLib()
  }

  /** Executor to run service operations on a background thread. */
  private val executor: ExecutorService = Executors.newSingleThreadExecutor()

  @Test
  fun client_startedSession_handshakesWithServer() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService = FakeService(executor, serverConfig) { it }

    val responseObserver = mock<OakSessionStreamObserver>()

    client.startSession(responseObserver) { fakeService.start(it) }

    fakeService.await()
    verify(responseObserver).onSessionOpen(any())
  }

  @Test
  fun client_startedSession_getsServerAppResponse() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService =
      FakeService(executor, serverConfig) { "PONG: ${it.toStringUtf8()}".toByteString() }

    val responseObserver = mock<OakSessionStreamObserver>()
    val clientStreamCaptor = argumentCaptor<StreamObserver<ByteString>>()
    val responseCaptor = argumentCaptor<ByteString>()

    client.startSession(responseObserver) { fakeService.start(it) }
    fakeService.await()

    verify(responseObserver).onSessionOpen(clientStreamCaptor.capture())
    val clientStream = clientStreamCaptor.lastValue

    clientStream.onNext("Hello World".toByteString())
    fakeService.await()

    verify(responseObserver).onNext(responseCaptor.capture())

    assertEquals(responseCaptor.lastValue.toStringUtf8(), "PONG: Hello World")
  }

  @Test
  fun client_startedSession_getsServerMultipleAppResponses() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService =
      FakeService(executor, serverConfig) { "PONG: ${it.toStringUtf8()}".toByteString() }

    val responseObserver = mock<OakSessionStreamObserver>()
    val clientStreamCaptor = argumentCaptor<StreamObserver<ByteString>>()
    val responseCaptor = argumentCaptor<ByteString>()

    client.startSession(responseObserver) { fakeService.start(it) }
    fakeService.await()

    verify(responseObserver).onSessionOpen(clientStreamCaptor.capture())
    val clientStream = clientStreamCaptor.lastValue

    clientStream.onNext("Hello World".toByteString())
    clientStream.onNext("Hello World 2".toByteString())
    clientStream.onNext("Hello World 3".toByteString())
    fakeService.await()

    verify(responseObserver, times(3)).onNext(responseCaptor.capture())
    assertEquals(
      responseCaptor.allValues.map { it.toStringUtf8() },
      listOf("PONG: Hello World", "PONG: Hello World 2", "PONG: Hello World 3"),
    )
  }

  @Test
  fun client_immediateServerError_returnsError() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())

    val responseObserver = mock<OakSessionStreamObserver>()

    val serverException = RuntimeException("Didn't connect")
    val mockToServer = mock<StreamObserver<SessionRequest>>()

    client.startSession(responseObserver) {
      executor.execute { it.onError(serverException) }
      mockToServer
    }
    executor.await()

    verify(responseObserver).onError(serverException)
    verify(responseObserver, never()).onSessionOpen(any())
  }

  @Test
  fun client_serverApplicationError_returnsError() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeAppException = RuntimeException("oops")
    val fakeService = FakeService(executor, serverConfig) { throw fakeAppException }

    val responseObserver = mock<OakSessionStreamObserver>()
    val clientStreamCaptor = argumentCaptor<StreamObserver<ByteString>>()

    client.startSession(responseObserver) { fakeService.start(it) }
    fakeService.await()

    verify(responseObserver).onSessionOpen(clientStreamCaptor.capture())
    val clientStream = clientStreamCaptor.lastValue

    clientStream.onNext("Hello World".toByteString())
    fakeService.await()

    verify(responseObserver).onError(fakeAppException)
  }

  private fun unattestedConfig() =
    OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN)

  private fun unattestedConfigProvider() = Provider { unattestedConfig() }

  private fun String.toByteString() = ByteString.copyFrom(this, StandardCharsets.UTF_8)

  /**
   * The fake service to use for tests. It does a handshake and responds to app messages using the
   * provided application implementation function.
   */
  class FakeService(
    val executor: ExecutorService,
    val sessionConfig: OakSessionConfigBuilder,
    val application: (ByteString) -> ByteString,
  ) : StreamObserver<SessionRequest> {
    private lateinit var responses: StreamObserver<SessionResponse>

    // Wait for the single-threaded service to finish by submitting a job and then
    // waiting on it.
    fun await() = executor.await()

    fun start(responses: StreamObserver<SessionResponse>): StreamObserver<SessionRequest> {
      this.responses = responses
      return this
    }

    private val serverSession = OakServerSession(sessionConfig)

    override fun onNext(request: SessionRequest) {
      executor.execute {
        if (serverSession.isOpen) {
          check(serverSession.putIncomingMessage(request))
          val decrypted = checkNotNull(serverSession.read().getOrNull()).plaintext
          val response =
            try {
              application(decrypted)
            } catch (e: Exception) {
              responses.onError(e)
              return@execute
            }
          val pt = PlaintextMessage.newBuilder().setPlaintext(response).build()
          serverSession.write(pt)
          val encryptedResponse = checkNotNull(serverSession.outgoingMessage.getOrNull())
          responses.onNext(encryptedResponse)
        } else {
          check(serverSession.putIncomingMessage(request))
          serverSession.outgoingMessage.getOrNull()?.let { responses.onNext(it) }
        }
      }
    }

    override fun onError(t: Throwable) {
      executor.execute { responses.onError(t) }
    }

    override fun onCompleted() {
      executor.execute { responses.onCompleted() }
    }
  }

  companion object {
    private fun ExecutorService.await() = submit {}.get()
  }
}

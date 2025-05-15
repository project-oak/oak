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
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import javax.inject.Provider
import kotlin.jvm.optionals.getOrNull
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4
import org.mockito.kotlin.any
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

  @Test
  fun client_startedSession_handshakesWithServer() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService = FakeService(serverConfig) { it }

    val done = CompletableFuture<Void>()
    val responseObserver =
      object : OakSessionStreamObserver {
        override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
          done.complete(null)
        }

        override fun onNext(response: ByteString) {}

        override fun onError(t: Throwable) {}

        override fun onCompleted() {}
      }

    client.startSession(responseObserver) { fakeService.start(it) }

    done.get(10, TimeUnit.SECONDS)
  }

  @Test
  fun client_startedSession_providesUnderlyingSession() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService = FakeService(serverConfig) { it }

    val done = CompletableFuture<Void>()
    val session = CompletableFuture<OakClientSession>()

    val responseObserver =
      object : OakSessionStreamObserver {
        override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
          session.complete(
            (clientRequests as StreamObserverSessionClient.ClientSessionAccess).oakClientSession
          )
          done.complete(null)
        }

        override fun onNext(response: ByteString) {}

        override fun onError(t: Throwable) {}

        override fun onCompleted() {}
      }

    client.startSession(responseObserver) { fakeService.start(it) }

    done.get(10, TimeUnit.SECONDS)
    assertTrue(session.get(10, TimeUnit.SECONDS).isOpen)
  }

  @Test
  fun client_startedSession_getsServerAppResponse() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService = FakeService(serverConfig) { "PONG: ${it.toStringUtf8()}".toByteString() }

    val responses = mutableListOf<ByteString>()
    val done = CompletableFuture<Void>()
    val responseObserver =
      object : OakSessionStreamObserver {
        lateinit var response: ByteString
        lateinit var clientRequests: StreamObserver<ByteString>

        override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
          this.clientRequests = clientRequests
          clientRequests.onNext("Hello World".toByteString())
          clientRequests.onCompleted()
        }

        override fun onNext(response: ByteString) {
          responses.add(response)
        }

        override fun onError(t: Throwable) {}

        override fun onCompleted() {
          done.complete(null)
        }
      }

    client.startSession(responseObserver) { fakeService.start(it) }
    done.get(10, TimeUnit.SECONDS)

    assertEquals(responses.map { it.toStringUtf8() }, listOf("PONG: Hello World"))
  }

  @Test
  fun client_startedSession_getsServerMultipleAppResponses() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val serverConfig = unattestedConfig()
    val fakeService = FakeService(serverConfig) { "PONG: ${it.toStringUtf8()}".toByteString() }

    val responses = mutableListOf<ByteString>()
    val done = CompletableFuture<Void>()
    val responseObserver =
      object : OakSessionStreamObserver {
        lateinit var response: ByteString

        override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
          // Order will be preserved because the fake server executors are single-threaded.
          clientRequests.onNext("Hello World".toByteString())
          clientRequests.onNext("Hello World 2".toByteString())
          clientRequests.onNext("Hello World 3".toByteString())
          clientRequests.onCompleted()
        }

        override fun onNext(response: ByteString) {
          responses.add(response)
        }

        override fun onError(t: Throwable) {}

        override fun onCompleted() {
          done.complete(null)
        }
      }

    client.startSession(responseObserver) { fakeService.start(it) }
    done.get(10, TimeUnit.SECONDS)

    assertEquals(
      responses.map { it.toStringUtf8() },
      listOf("PONG: Hello World", "PONG: Hello World 2", "PONG: Hello World 3"),
    )
  }

  @Test
  fun client_immediateServerError_returnsError() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())

    val responseObserver = mock<OakSessionStreamObserver>()

    val serverException = RuntimeException("Didn't connect")

    val executor = Executors.newSingleThreadExecutor()
    client.startSession(responseObserver) {
      executor.execute { it.onError(serverException) }
      mock<StreamObserver<SessionRequest>>()
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
    val fakeService = FakeService(serverConfig) { throw fakeAppException }

    val responseFuture = CompletableFuture<Throwable>()
    val responseObserver =
      object : OakSessionStreamObserver {

        override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
          clientRequests.onNext("Big badaboom".toByteString())
        }

        override fun onNext(response: ByteString) {}

        override fun onError(t: Throwable) {
          responseFuture.complete(t)
        }

        override fun onCompleted() {}
      }

    client.startSession(responseObserver) { fakeService.start(it) }
    val exception = responseFuture.get(10, TimeUnit.SECONDS)
    assertEquals(exception, fakeAppException)
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
    val sessionConfig: OakSessionConfigBuilder,
    val application: (ByteString) -> ByteString,
  ) : StreamObserver<SessionRequest> {
    private var requestExecutor = Executors.newSingleThreadExecutor()
    private var responseExecutor = Executors.newSingleThreadExecutor()

    private lateinit var responses: StreamObserver<SessionResponse>

    fun start(responses: StreamObserver<SessionResponse>): StreamObserver<SessionRequest> {
      this.responses = responses
      return this
    }

    private val serverSession = OakServerSession(sessionConfig)

    override fun onNext(request: SessionRequest) {
      requestExecutor.execute {
        if (serverSession.isOpen) {
          check(serverSession.putIncomingMessage(request))
          val decrypted = checkNotNull(serverSession.read().getOrNull()).plaintext
          val response =
            try {
              application(decrypted)
            } catch (e: Exception) {
              responseExecutor.execute { responses.onError(e) }
              return@execute
            }
          val pt = PlaintextMessage.newBuilder().setPlaintext(response).build()
          serverSession.write(pt)
          val encryptedResponse = checkNotNull(serverSession.outgoingMessage.getOrNull())
          responseExecutor.execute { responses.onNext(encryptedResponse) }
        } else {
          check(serverSession.putIncomingMessage(request))
          serverSession.outgoingMessage.getOrNull()?.let {
            responseExecutor.execute { responses.onNext(it) }
          }
        }
      }
    }

    override fun onError(t: Throwable) {
      requestExecutor.execute { responseExecutor.execute { responses.onError(t) } }
    }

    override fun onCompleted() {
      requestExecutor.execute { responseExecutor.execute { responses.onCompleted() } }
    }
  }

  companion object {
    private fun ExecutorService.await() = submit {}.get()
  }
}

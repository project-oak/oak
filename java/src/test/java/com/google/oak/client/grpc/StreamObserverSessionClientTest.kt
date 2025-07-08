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
import io.grpc.Status
import io.grpc.StatusRuntimeException
import io.grpc.inprocess.InProcessChannelBuilder
import io.grpc.inprocess.InProcessServerBuilder
import io.grpc.stub.StreamObserver
import java.nio.charset.StandardCharsets
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutionException
import java.util.concurrent.Executors
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import javax.inject.Provider
import kotlin.AutoCloseable
import kotlin.jvm.optionals.getOrNull
import kotlin.test.assertFailsWith
import org.junit.After
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

@RunWith(JUnit4::class)
@SuppressWarnings("CheckReturnValue")
class StreamObserverSessionClientTest {
  init {
    OakServerSession.loadNativeLib()
    OakClientSession.loadNativeLib()
  }

  val serverName = InProcessServerBuilder.generateName()
  val channel =
    InProcessChannelBuilder.forName(serverName)
      .executor(Executors.newSingleThreadExecutor())
      .build()
  val stub = TestServiceGrpc.newStub(channel)

  @After
  fun cleanup() {
    channel.shutdown()
  }

  @Test
  fun client_startedSession_handshakesWithServer() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService = FakeServiceImpl(unattestedConfigProvider()) { it }
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()
      client.startSession(responseObserver) { stub.startSession(it) }

      responseObserver.awaitOpen().onCompleted()
      responseObserver.awaitCompleted()
    }
  }

  @Test
  fun client_startedSession_handshakesWithServer_checkForSessionLeaks() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService = FakeServiceImpl(unattestedConfigProvider()) { it }
    startServer(fakeService).use {
      repeat(2000) {
        val responseObserver = WaitingResponseObserver()
        client.startSession(responseObserver) { stub.startSession(it) }

        responseObserver.awaitOpen().onCompleted()
        responseObserver.awaitCompleted()
      }
    }
  }

  @Test
  fun client_startedSession_providesUnderlyingSession() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService = FakeServiceImpl(unattestedConfigProvider()) { it }
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()
      client.startSession(responseObserver) { stub.startSession(it) }

      val clientRequests = responseObserver.awaitOpen()
      assertTrue(
        (clientRequests as StreamObserverSessionClient.ClientSessionAccess).oakClientSession.isOpen
      )
      clientRequests.onCompleted()
      responseObserver.awaitCompleted()
      assertFailsWith<IllegalStateException> {
        (clientRequests as StreamObserverSessionClient.ClientSessionAccess).oakClientSession.isOpen
      }
    }
  }

  @Test
  fun client_startedSession_getsServerAppResponse() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService =
      FakeServiceImpl(unattestedConfigProvider()) { "PONG: ${it.toStringUtf8()}".toByteString() }
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()
      client.startSession(responseObserver) { stub.startSession(it) }

      val clientRequests = responseObserver.awaitOpen()
      clientRequests.onNext("Hello World".toByteString())
      clientRequests.onCompleted()

      val responses = responseObserver.awaitCompleted()
      assertEquals(responses.map { it.toStringUtf8() }, listOf("PONG: Hello World"))
    }
  }

  @Test
  fun client_startedSession_getsServerMultipleAppResponses() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService =
      FakeServiceImpl(unattestedConfigProvider()) { "PONG: ${it.toStringUtf8()}".toByteString() }
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()
      client.startSession(responseObserver) { stub.startSession(it) }

      val clientRequests = responseObserver.awaitOpen()
      clientRequests.onNext("Hello World".toByteString())
      clientRequests.onNext("Hello World 2".toByteString())
      clientRequests.onNext("Hello World 3".toByteString())
      clientRequests.onCompleted()

      assertEquals(
        responseObserver.awaitCompleted().map { it.toStringUtf8() },
        listOf("PONG: Hello World", "PONG: Hello World 2", "PONG: Hello World 3"),
      )
    }
  }

  @Test
  fun client_immediateServerError_returnsError() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val responseObserver = WaitingResponseObserver()

    client.startSession(responseObserver) { stub.startSession(it) }

    val exception = assertFailsWith<StatusRuntimeException> { responseObserver.awaitOpen() }
    assertEquals(exception.status.code, Status.Code.UNAVAILABLE)
  }

  @Test
  fun client_serverApplicationError_returnsError() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService = FakeServiceImpl(unattestedConfigProvider()) { throw RuntimeException("oops") }
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()
      client.startSession(responseObserver) { stub.startSession(it) }

      val clientRequests = responseObserver.awaitOpen()
      clientRequests.onNext("Big badaboom".toByteString())

      val exception = assertFailsWith<StatusRuntimeException> { responseObserver.awaitCompleted() }
      assertEquals(exception.status.code, Status.Code.UNKNOWN)
    }
  }

  @Test
  fun client_cancellingUnopenSession_cancels() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val responseObserver = WaitingResponseObserver()
    val fakeService = FakeServiceImpl(unattestedConfigProvider())
    fakeService.stopResponding = true
    startServer(fakeService).use {
      val cancelHandle = client.startSession(responseObserver) { stub.startSession(it) }

      val cancelCause = RuntimeException("fake cause")
      cancelHandle.cancel("test cancel", cancelCause)
      val exception = assertFailsWith<StatusRuntimeException> { responseObserver.awaitCompleted() }
      assertEquals(exception.status.code, Status.Code.CANCELLED)
      assertEquals(
        (fakeService.error.get() as StatusRuntimeException).status.code,
        Status.Code.CANCELLED,
      )
    }
  }

  @Test
  fun client_cancellingActiveSession_cancels() {
    val client = StreamObserverSessionClient(unattestedConfigProvider())
    val fakeService = FakeServiceImpl(unattestedConfigProvider())
    startServer(fakeService).use {
      val responseObserver = WaitingResponseObserver()

      val cancelHandle = client.startSession(responseObserver) { stub.startSession(it) }

      val clientRequests = responseObserver.awaitOpen()
      clientRequests.onNext("Hello World".toByteString())
      // Still active...

      cancelHandle.cancel("test cancel", null)
      val exception = assertFailsWith<StatusRuntimeException> { responseObserver.awaitCompleted() }
      assertEquals(exception.status.code, Status.Code.CANCELLED)
      assertEquals(
        (fakeService.error.get() as? StatusRuntimeException)?.status?.code,
        Status.Code.CANCELLED,
      )
    }
  }

  /** A helper for tests that provides the typical wait points needed for a test. */
  class WaitingResponseObserver : StreamObserverSessionClient.OakSessionStreamObserver {
    private val done = CompletableFuture<List<ByteString>>()
    private val openFuture = CompletableFuture<StreamObserver<ByteString>>()
    private val responses = mutableListOf<ByteString>()

    override fun onSessionOpen(clientRequests: StreamObserver<ByteString>) {
      openFuture.complete(clientRequests)
    }

    override fun onNext(response: ByteString) {
      responses += response
    }

    override fun onError(t: Throwable) {
      openFuture.completeExceptionally(t)
      done.completeExceptionally(t)
    }

    override fun onCompleted() {
      openFuture.completeExceptionally(RuntimeException("completed before open"))
      done.complete(responses)
    }

    private fun <T> Future<T>.getForTesting(): T =
      try {
        get(10, TimeUnit.SECONDS)
      } catch (e: ExecutionException) {
        throw e.cause!!
      }

    fun awaitOpen(): StreamObserver<ByteString> = openFuture.getForTesting()

    fun awaitCompleted(): List<ByteString> = done.getForTesting()
  }

  private fun unattestedConfigProvider() = Provider {
    OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN)
  }

  private fun String.toByteString() = ByteString.copyFrom(this, StandardCharsets.UTF_8)

  fun startServer(serviceImpl: TestServiceGrpc.TestServiceImplBase): AutoCloseable =
    InProcessServerBuilder.forName(serverName)
      .executor(Executors.newSingleThreadExecutor())
      .addService(serviceImpl)
      .build()
      .start()
      .run { AutoCloseable { shutdown() } }

  /**
   * The fake service to use for tests. It does a handshake and responds to app messages using the
   * provided application implementation function.
   *
   * @param sessionConfig the server session to use (should match test client)
   * @param application a bytes-in bytes-out application impl. Defaults to empty responses.
   */
  class FakeServiceImpl(
    val sessionConfigProvider: Provider<OakSessionConfigBuilder>,
    val application: (ByteString) -> ByteString = { ByteString.EMPTY },
  ) : TestServiceGrpc.TestServiceImplBase() {
    val error = CompletableFuture<Throwable>()
    /** Set to true to fake a hanging server. */
    var stopResponding = false

    override fun startSession(
      responses: StreamObserver<SessionResponse>
    ): StreamObserver<SessionRequest> {
      val serverSession = OakServerSession(sessionConfigProvider.get())
      return object : StreamObserver<SessionRequest> {
        override fun onNext(request: SessionRequest) {
          if (stopResponding) return

          if (serverSession.isOpen) {
            check(serverSession.putIncomingMessage(request))
            val decrypted = checkNotNull(serverSession.read().getOrNull()).plaintext
            val response = application(decrypted)
            val pt = PlaintextMessage.newBuilder().setPlaintext(response).build()
            serverSession.write(pt)
            val encryptedResponse = checkNotNull(serverSession.outgoingMessage.getOrNull())
            responses.onNext(encryptedResponse)
          } else {
            check(serverSession.putIncomingMessage(request))
            serverSession.outgoingMessage.getOrNull()?.let { responses.onNext(it) }
          }
        }

        override fun onError(t: Throwable) {
          error.complete(t)
          responses.onError(t)
        }

        override fun onCompleted() {
          responses.onCompleted()
        }
      }
    }
  }
}

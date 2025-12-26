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

import com.google.errorprone.annotations.CanIgnoreReturnValue
import com.google.oak.session.OakClientSession
import com.google.oak.session.OakSessionConfigBuilder
import com.google.oak.session.OakSessionException
import com.google.oak.session.v1.PlaintextMessage
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import com.google.protobuf.ByteString
import io.grpc.stub.ClientCallStreamObserver
import io.grpc.stub.StreamObserver
import java.util.Optional
import javax.inject.Provider

/**
 * An asynchronous client for Oak Session based on StreamObservers.
 *
 * It acts as a facade between a service speaking the Oak Session protocol and a client that works
 * directly with unencrypted byte streams.
 *
 * You can create a single instance of this class, and then use the [startSession] method to begin
 * as many new streaming sessions as needed.
 *
 * @param sessionConfigBuilderProvider provides a new OakSessionConfigBuilder instance for each new
 *   established session.
 */
class StreamObserverSessionClient(
  private val sessionConfigBuilderProvider: Provider<OakSessionConfigBuilder>
) {
  /**
   * Start a new Oak Session.
   *
   * This class is an adapter between the underlying Oak Protocol messages and the raw byte messages
   * that the application wants.
   *
   * The interface to the client is [StreamObserver<ByteString>] for both requests and responses and
   * follows the documented conventions of that interface.
   *
   * Example Usage:
   * ```
   *
   * val responseObserver = object : StreamObserver<ByteString> {
   *   override fun onSessionOpen(requests: StreamObserver<ByteString>) {
   *     requests.onNext(ByteString.copyFrom("My first and only request"))
   *     requests.onCompleted()
   *   }
   *   override fun onNext(response: ByteString) {
   *     println("Decrypted server response: $response")
   *   }
   *   override fun onError(t: Throwable) = Unit
   *   override fun onCompleted() {
   *     println("Server has finished responding.")
   *   }
   * }
   *
   * val stub = getMyOakServerStub();
   *
   * val configProvider = Provider {
   *   OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN)
   * }
   *
   * val client = StreamObserverSessionClient(configProvider)
   *
   * client.startSession(
   *   responseObserver,
   *   streamStarter = stub::invokeOakMethod(it)
   * )
   * ```
   *
   * Note: Regardless of the underlying gRPC implementation, this client does not allow the sending
   * of client requests once it's received a half-close from the server.
   *
   * @param sessionStreamObserver an implementation of [OakSessionStreamObesrver] that will provide
   *   decrypted responses to the caller, and that will provide an observer for sending requests to
   *   the server once the session is established.
   * @param streamStarter is used to start a new bidirectional streaming session. In typical uses,
   *   you'll call a gRPC `asyncStub` method that implements a bi-directional streaming endpoint
   *   using the Oak Session protocol.
   */
  @CanIgnoreReturnValue
  fun startSession(
    sessionStreamObserver: OakSessionStreamObserver,
    streamStarter: (StreamObserver<SessionResponse>) -> StreamObserver<SessionRequest>,
  ): SessionHandle {
    return ServerStreamObserver.startSession(
      OakClientSession(sessionConfigBuilderProvider.get()),
      sessionStreamObserver,
      { streamStarter(it) },
    )
  }

  /**
   * A handle to an active session.
   *
   * A session handle contains coarse-grained control to the session. For example, it can be used to
   * connect an active session to a component with a lifecycle, which can call [cancel] to clean up
   * an active session that's no longer needed.
   */
  interface SessionHandle {
    /**
     * Cancel the session in any state.
     *
     * This will cancel the underlying gRPC stream, and clean up any other resources. The session
     * should not be used anymore after calling this.
     */
    fun cancel(message: String? = null, cause: Throwable? = null)
  }

  /**
   * The application-level request/response logic handlers.
   *
   * It combines client request sending and response receiving logic:
   * * The [StreamObserver<ByteString>] implementation will receive decrypted server requests once
   *   the session has been opened.
   * * The [onSessionOpen] callback will provide an instance of a client request observer that can
   *   accept plaintext requests, encrypt them, and send them to the server.
   */
  interface OakSessionStreamObserver : StreamObserver<ByteString> {
    /** Called when the session is open, providing a request sender. */
    fun onSessionOpen(clientRequests: StreamObserver<ByteString>)
  }

  /**
   * An interface for providing internal [OakClientSession].
   *
   * The [`onSessionOpen`] callback StreamObserver will also implement this interface, so if you
   * really need to get access to the underlying session, you can cast the instance to this
   * interface.
   *
   * This isn't normally needed, and is for advanced features.
   */
  interface ClientSessionAccess {
    /** Get the underlying OakClientSession of the class implementing this. */
    val oakClientSession: OakClientSession
  }

  /**
   * The ServerStream observer provided to the server to receive responses.
   *
   * This observer will handle the handshake sequence.
   *
   * When the handshake completes, the provided [`OakSessionStreamObserver.onSessionOpen`] will be
   * invoked, passing a ready-to-use client stream observer back to the caller.
   *
   * Once the session is open, it will decrypt incoming application messages and forward them on to
   * the client.
   */
  private class ServerStreamObserver
  private constructor(
    private val oakClientSession: OakClientSession,
    private val sessionStreamObserver: OakSessionStreamObserver,
  ) : StreamObserver<SessionResponse> {
    private lateinit var toServer: StreamObserver<SessionRequest>

    override fun onNext(response: SessionResponse) {
      // Handles all incoming responses from the server.
      // They're either intiialization requests during the init sequence or
      // application requests once session is open.
      if (oakClientSession.isOpen) {
        handleAppResponse(response)
      } else {
        handleInitResponse(response)
      }
    }

    override fun onCompleted() {
      // We just forward completion events.
      oakClientSession.close()
      sessionStreamObserver.onCompleted()
    }

    override fun onError(t: Throwable) {
      // We just forward error events.
      oakClientSession.close()
      sessionStreamObserver.onError(t)
    }

    /** When the session is open, we simply decrypt the response and forward to client. */
    private fun handleAppResponse(response: SessionResponse) {
      if (!oakClientSession.putIncomingMessage(response)) {
        throw OakSessionException(
          "Expected encrypted message response but received: ${response.responseCase}"
        )
      }

      sessionStreamObserver.onNext(
        oakClientSession.read().assert("Decrypted message was not available").plaintext
      )
    }

    /** If the session is not open, we perform the next step of the initialize sequence. */
    private fun handleInitResponse(response: SessionResponse) {
      if (!oakClientSession.putIncomingMessage(response)) {
        throw OakSessionException(
          "Expected initialization response but received: ${response.responseCase}"
        )
      }

      if (oakClientSession.isOpen) {
        sessionStreamObserver.onSessionOpen(
          ClientToServerStreamObserver(oakClientSession, toServer)
        )
      } else {
        val nextInitRequest =
          oakClientSession.outgoingMessage.assert(
            "Session is not open, but no initialization message is available."
          )
        toServer.onNext(nextInitRequest)
      }
    }

    companion object {
      fun startSession(
        oakClientSession: OakClientSession,
        sessionStreamObserver: OakSessionStreamObserver,
        streamStarter: (StreamObserver<SessionResponse>) -> StreamObserver<SessionRequest>,
      ): SessionHandle {
        val initMessage =
          oakClientSession.outgoingMessage.assert("Client did not have initial message.")

        val observer = ServerStreamObserver(oakClientSession, sessionStreamObserver)
        observer.toServer = streamStarter(observer)
        observer.toServer.onNext(initMessage)
        return object : SessionHandle {
          override fun cancel(message: String?, cause: Throwable?) =
            (observer.toServer as ClientCallStreamObserver).cancel(message, cause)
        }
      }
    }
  }

  companion object {
    private fun ByteString.toPlaintextMessage() =
      PlaintextMessage.newBuilder().setPlaintext(this).build()

    private fun <T : Any> Optional<T>.assert(msg: String) = orElseThrow {
      AssertionError("Internal library implementation error. Please report a bug: $msg")
    }

    private fun ClientToServerStreamObserver(
      oakClientSession: OakClientSession,
      toServer: StreamObserver<SessionRequest>,
    ): StreamObserver<ByteString> =
      object : StreamObserver<ByteString>, ClientSessionAccess {
        override val oakClientSession: OakClientSession = oakClientSession

        private var completed = false

        override fun onNext(clientRequest: ByteString) {
          check(!completed) { "This StreamObserver has been completed." }
          oakClientSession.write(clientRequest.toPlaintextMessage())

          toServer.onNext(
            oakClientSession.outgoingMessage.assert(
              "Encrypted message was written but not available"
            )
          )
        }

        override fun onCompleted() {
          check(!completed) { "This StreamObserver has been completed." }
          toServer.onCompleted()
          completed = true
        }

        override fun onError(t: Throwable) {
          check(!completed) { "This StreamObserver has been completed." }
          toServer.onError(t)
          completed = true
        }
      }
  }
}

//
// Copyright 2024 The Project Oak Authors
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

package com.google.oak.client

import com.google.oak.services.OakSessionV1ServiceGrpc
import com.google.oak.session.OakServerSession
import com.google.oak.session.OakSessionConfigBuilder
import com.google.oak.session.OakSessionConfigBuilder.AttestationType
import com.google.oak.session.OakSessionConfigBuilder.HandshakeType
import com.google.oak.session.v1.PlaintextMessage
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import com.google.oak.transport.GrpcSessionV1ClientTransport
import com.google.protobuf.ByteString
import io.grpc.ManagedChannel
import io.grpc.Server
import io.grpc.inprocess.InProcessChannelBuilder
import io.grpc.inprocess.InProcessServerBuilder
import io.grpc.stub.StreamObserver
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlinx.coroutines.test.runTest
import org.junit.After
import org.junit.Before
import org.junit.Test

class TestSessionServer : OakSessionV1ServiceGrpc.OakSessionV1ServiceImplBase() {
  private var session: OakServerSession

  init {
    OakServerSession.loadNativeLib()
    session =
      OakServerSession(OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN))
  }

  override fun stream(
    responseObserver: StreamObserver<SessionResponse>
  ): StreamObserver<SessionRequest> {
    return object : StreamObserver<SessionRequest> {
      override fun onNext(request: SessionRequest) {
        if (session.isOpen()) {
          assertTrue(session.putIncomingMessage(request))
          val incomingPlaintext = session.read().get()
          session.write(
            PlaintextMessage.newBuilder()
              .setPlaintext(
                ByteString.copyFromUtf8(incomingPlaintext.getPlaintext().toStringUtf8().reversed())
              )
              .build()
          )
        } else {
          assertTrue(session.putIncomingMessage(request))
        }

        val outMessage = session.getOutgoingMessage()
        if (outMessage.isPresent()) {
          responseObserver.onNext(outMessage.get())
        }
      }

      override fun onError(t: Throwable) {
        responseObserver.onError(t)
      }

      override fun onCompleted() {
        responseObserver.onCompleted()
      }
    }
  }
}

class OakSessionClientTest {
  private lateinit var server: Server
  private lateinit var channel: ManagedChannel

  @Before
  fun setUp() {
    println("SETUP")
    val serverName = InProcessServerBuilder.generateName()

    // Create a new server and start it.
    server =
      InProcessServerBuilder.forName(serverName)
        .directExecutor()
        .addService(TestSessionServer())
        .build()
        .start()

    // Create a channel for the client to connect to the server.
    channel = InProcessChannelBuilder.forName(serverName).directExecutor().build()
  }

  @After
  fun tearDown() {
    // Shut down the server and channel after each test.
    channel.shutdownNow()
    server.shutdown()
  }

  @Test
  fun testConnect() = runTest {
    val transport = GrpcSessionV1ClientTransport(channel, this)
    val client = OakSessionClient(transport)
    val oakChannel = client.newChannel()
    oakChannel.write("oak".toByteArray())
    // To test that messages can be written to the channel asynchronously but will be read in the
    // correct order.
    oakChannel.write("ignored".toByteArray())
    assertEquals("kao", oakChannel.read().toString(Charsets.UTF_8))
    oakChannel.close()
  }
}

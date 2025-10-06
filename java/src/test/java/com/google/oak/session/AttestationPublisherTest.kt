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

package com.google.oak.session

import com.google.common.truth.Truth.assertThat
import com.google.oak.Variant
import com.google.oak.attestation.v1.Assertion
import com.google.oak.attestation.v1.Endorsements
import com.google.oak.attestation.v1.EventLog
import com.google.oak.attestation.v1.Evidence
import com.google.oak.session.v1.EndorsedEvidence
import com.google.oak.session.v1.SessionBinding
import com.google.protobuf.ByteString
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

@RunWith(JUnit4::class)
class AttestationPublisherTest {

  @Test
  fun oakSession_withJVMAttestationPublisher_publishes() {
    // Arrange: Set up of the session configs with a client publisher.
    var publishedEvidence: Map<String, EndorsedEvidence>? = null
    var publishedBindings: Map<String, SessionBinding>? = null
    var publishedHandshakeHash: ByteArray? = null

    val publisher =
      object : AttestationPublisher {
        override fun publish(
          evidence: Map<String, ByteArray>,
          bindings: Map<String, ByteArray>,
          handshakeHash: ByteArray,
        ) {
          publishedEvidence = evidence.mapValues { (_, value) -> EndorsedEvidence.parseFrom(value) }
          publishedBindings = bindings.mapValues { (_, value) -> SessionBinding.parseFrom(value) }
          publishedHandshakeHash = handshakeHash
        }
      }

    val serverConfig = nativeCreateServerConfigBuilder()
    val clientConfig = nativeCreateClientConfigBuilder(publisher)

    val client = OakClientSession(clientConfig)
    val server = OakServerSession(serverConfig)

    /// Act: Perform a handshake, which should publish
    doHandshake(client, server)

    // Assert: Ensure that the publisher received the evidence and assertions
    // created by the native test helper.
    val expectedEndorsement = createVariant(id = "testing", value = "fake endorsement")
    assertThat(publishedEvidence)
      .containsExactly(
        "test id",
        createEndorsedEventsWithSingleEventAndEndorsement("fake event", expectedEndorsement),
      )

    assertThat(publishedBindings?.get("test id")!!.binding).isNotEmpty()
    assertThat(publishedHandshakeHash).isNotEmpty()
  }

  private fun String.toByteString() = ByteString.copyFromUtf8(this)

  private fun createVariant(id: String, value: String) =
    Variant.newBuilder().setId(id.toByteString()).setValue(value.toByteString()).build()

  private fun createAssertionWithContent(content: String) =
    Assertion.newBuilder().setContent(content.toByteString())

  private fun createEndorsedEventsWithSingleEventAndEndorsement(
    event: String,
    endorsement: Variant,
  ) =
    EndorsedEvidence.newBuilder()
      .setEndorsements(Endorsements.newBuilder().addEvents(endorsement))
      .setEvidence(
        Evidence.newBuilder()
          .setEventLog(EventLog.newBuilder().addEncodedEvents(event.toByteString()))
      )
      .build()

  private fun doHandshake(clientSession: OakClientSession, serverSession: OakServerSession) {
    while (!clientSession.isOpen() || !serverSession.isOpen()) {
      val request = clientSession.getOutgoingMessage()
      assertThat(serverSession.putIncomingMessage(request.get())).isTrue()
      val response = serverSession.getOutgoingMessage()
      assertThat(clientSession.putIncomingMessage(response.get())).isTrue()
    }
  }

  companion object {
    init {
      System.loadLibrary("attestation_publisher_test_jni")
      System.loadLibrary("oak_client_session_jni")
      System.loadLibrary("oak_server_session_jni")
      println("Loaded library")
    }

    @JvmStatic private external fun nativeCreateServerConfigBuilder(): OakSessionConfigBuilder

    @JvmStatic
    private external fun nativeCreateClientConfigBuilder(
      publisher: AttestationPublisher
    ): OakSessionConfigBuilder
  }
}

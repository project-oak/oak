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

import com.google.oak.session.OakClientSession
import com.google.oak.session.v1.PlaintextMessage
import com.google.oak.session.v1.SessionResponse
import com.google.oak.transport.SessionTransport
import com.google.protobuf.ByteString

/**
 * Class defining a bidi-streaming channel that can be used for secure communication with the Oak
 * peer.
 */
class OakClientChannel(
  private val session: OakClientSession,
  private val transport: SessionTransport,
) {
  suspend fun read(): ByteArray {
    val inBytes = transport.read()
    session.putIncomingMessage(SessionResponse.parseFrom(inBytes))
    return session.read().orElseThrow().plaintext.toByteArray()
  }

  suspend fun write(message: ByteArray) {
    session.write(PlaintextMessage.newBuilder().setPlaintext(ByteString.copyFrom(message)).build())
    val outMessage = session.getOutgoingMessage().orElseThrow()
    transport.write(outMessage.toByteArray())
  }
}

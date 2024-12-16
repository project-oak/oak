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
import com.google.oak.session.OakSessionException
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import com.google.oak.transport.SessionTransport

/** Client to establish and use a streaming Oak Session using the Noise protocol. */
class OakSessionClient(private val transport: SessionTransport<SessionRequest, SessionResponse>) {
  suspend fun newChannel(): OakClientChannel {
    val session = OakClientSession.createClientUnattested()
    while (!session.isOpen()) {
      val outMessage = session.getOutgoingMessage().orElseThrow()
      transport.write(outMessage)
      if (!session.isOpen()) {
        // Some protocols require the client to send a message that doesn't need to be answered by
        // the server before the session becomes open.
        val inMessage = transport.read()
        if (!session.putIncomingMessage(inMessage)) {
          throw OakSessionException("Unexpected message received during the handshake")
        }
      }
    }
    return OakClientChannel(session, transport)
  }
}

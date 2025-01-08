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

package com.google.oak.transport

import com.google.common.flogger.GoogleLogger
import com.google.oak.services.OakSessionV1ServiceGrpcKt
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import io.grpc.ManagedChannel
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onCompletion
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.receiveAsFlow

class GrpcSessionV1ClientTransport(val channel: ManagedChannel, val scope: CoroutineScope) :
  SessionTransport<SessionRequest, SessionResponse> {
  private val requests = Channel<SessionRequest>()
  private val responses = Channel<SessionResponse>()

  private val backgroundJob =
    OakSessionV1ServiceGrpcKt.OakSessionV1ServiceCoroutineStub(channel)
      .stream(requests.receiveAsFlow())
      .catch { e -> logger.atSevere().withCause(e).log("Failure in the session gRPC stream") }
      .onEach { responses.send(it) }
      .onCompletion {
        requests.cancel()
        responses.cancel()
      }
      .launchIn(scope)

  override suspend fun write(request: SessionRequest) {
    requests.send(request)
  }

  override suspend fun read(): SessionResponse {
    return responses.receive()
  }

  override fun close() {
    channel.shutdown()
    backgroundJob.cancel()
  }

  companion object {
    private val logger = GoogleLogger.forEnclosingClass()
  }
}

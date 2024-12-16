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

import com.google.oak.services.OakSessionV1ServiceGrpcKt
import com.google.oak.session.v1.SessionRequest
import com.google.oak.session.v1.SessionResponse
import io.grpc.ManagedChannelBuilder
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.flow.first

class GrpcSessionV1ClientTransport(val host: String, val port: Int) :
  SessionTransport<SessionRequest, SessionResponse> {
  private val channel =
    ManagedChannelBuilder.forAddress(this.host, this.port).usePlaintext().build()
  private val requestFlow = MutableSharedFlow<SessionRequest>()
  private val responseFlow: Flow<SessionResponse>

  init {
    val serviceStub = OakSessionV1ServiceGrpcKt.OakSessionV1ServiceCoroutineStub(channel)
    responseFlow = serviceStub.stream(requestFlow)
  }

  override suspend fun write(request: SessionRequest) {
    requestFlow.emit(request)
  }

  override suspend fun read(): SessionResponse {
    return responseFlow.first()
  }

  fun close() {
    channel.shutdown()
  }
}

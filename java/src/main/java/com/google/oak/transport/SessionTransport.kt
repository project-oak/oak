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

/** Transport layer for the Oak client session. */
interface SessionTransport<Request, Response> {
  /** Write the request into the transport layer. */
  suspend fun write(request: Request)

  /** Read a message from the transport layer. May block until a new message is received. */
  suspend fun read(): Response

  /**
   * Close the channel and free the underlying resources. Any reads or writes after this call will
   * fail.
   */
  fun close()
}

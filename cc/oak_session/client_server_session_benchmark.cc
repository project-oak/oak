/*
 * Copyright 2025 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <string>

#include "absl/log/check.h"
#include "absl/status/status_matchers.h"
#include "benchmark/benchmark.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "proto/session/session.pb.h"

namespace oak::session {
namespace {

using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;

class ClientServerSessionBench : public benchmark::Fixture {};

SessionConfig* TestConfig() {
  return SessionConfigBuilder(AttestationType::kUnattested,
                              HandshakeType::kNoiseNN)
      .Build();
}

std::string TestMessage(int size) {
  std::string message;
  message.reserve(size);
  for (int i = 0; i < size; i++) {
    message += i % 255;
  }
  return message;
}

void DoHandshake(ClientSession& client_session, ServerSession& server_session) {
  absl::StatusOr<std::optional<SessionRequest>> init =
      client_session.GetOutgoingMessage();
  QCHECK_OK(init);
  QCHECK(*init != std::nullopt);
  QCHECK_OK(server_session.PutIncomingMessage(**init));

  absl::StatusOr<std::optional<SessionResponse>> init_resp =
      server_session.GetOutgoingMessage();
  QCHECK_OK(init_resp);
  QCHECK(*init_resp != std::nullopt);
  QCHECK_OK(client_session.PutIncomingMessage(**init_resp));

  QCHECK(client_session.IsOpen());
  QCHECK(server_session.IsOpen());
}

BENCHMARK_DEFINE_F(ClientServerSessionBench, ClientEncryptServerDecrypt)
(benchmark::State& state) {
  auto client_session = ClientSession::Create(TestConfig());
  auto server_session = ServerSession::Create(TestConfig());

  DoHandshake(**client_session, **server_session);

  std::string test_message = TestMessage(state.range(0));
  for (auto iter : state) {
    v1::PlaintextMessage plaintext_message_request;
    plaintext_message_request.set_plaintext(test_message);

    QCHECK_OK((*client_session)->Write(plaintext_message_request));
    absl::StatusOr<std::optional<SessionRequest>> request =
        (*client_session)->GetOutgoingMessage();
    QCHECK_OK(request);
    QCHECK(*request != std::nullopt);

    QCHECK_OK((*server_session)->PutIncomingMessage(**request));
    absl::StatusOr<std::optional<v1::PlaintextMessage>> received_request =
        (*server_session)->Read();
    QCHECK_OK(received_request);
    QCHECK(*received_request != std::nullopt);

    QCHECK((**received_request).plaintext() ==
           plaintext_message_request.plaintext());
  }

  state.SetBytesProcessed(int64_t(state.iterations()) *
                          int64_t(state.range(0)));
}

BENCHMARK_REGISTER_F(ClientServerSessionBench, ClientEncryptServerDecrypt)
    ->Range(2, 2 << 21);

}  // namespace

}  // namespace oak::session

// Run the benchmark
BENCHMARK_MAIN();

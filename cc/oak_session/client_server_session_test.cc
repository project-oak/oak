/*
 * Copyright 2024 The Project Oak Authors
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

#include "absl/status/status_matchers.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/session/session.pb.h"

namespace oak::session {
namespace {

using ::absl_testing::IsOk;
using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::testing::Eq;
using ::testing::Ne;

void DoHandshake(ClientSession& client_session, ServerSession& server_session) {
  absl::StatusOr<std::optional<SessionRequest>> init =
      client_session.GetOutgoingMessage();
  ASSERT_THAT(init, IsOk());
  ASSERT_THAT(*init, Ne(std::nullopt));
  ASSERT_THAT(server_session.PutIncomingMessage(**init), IsOk());

  absl::StatusOr<std::optional<SessionResponse>> init_resp =
      server_session.GetOutgoingMessage();
  ASSERT_THAT(init_resp, IsOk());
  ASSERT_THAT(*init_resp, Ne(std::nullopt));
  ASSERT_THAT(client_session.PutIncomingMessage(**init_resp), IsOk());

  EXPECT_THAT(client_session.IsOpen(), Eq(true));
  EXPECT_THAT(server_session.IsOpen(), Eq(true));
}

TEST(ClientServerSessionTest, HandshakeSucceeds) {
  auto client_session = ClientSession::Create();
  auto server_session = ServerSession::Create();

  DoHandshake(**client_session, **server_session);
}

TEST(ClientServerSessionTest, AcceptEmptyOutgoingMessageResult) {
  auto client_session = ClientSession::Create();
  auto server_session = ServerSession::Create();

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOk());
  ASSERT_THAT(*request, Eq(std::nullopt));

  absl::StatusOr<std::optional<SessionResponse>> response =
      (*server_session)->GetOutgoingMessage();
  ASSERT_THAT(response, IsOk());
  ASSERT_THAT(*response, Eq(std::nullopt));
}

TEST(ClientServerSessionTest, AcceptEmptyReadResult) {
  auto client_session = ClientSession::Create();
  auto server_session = ServerSession::Create();

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<std::optional<std::string>> client_read =
      (*client_session)->Read();
  ASSERT_THAT(client_read, IsOk());
  ASSERT_THAT(*client_read, Eq(std::nullopt));

  absl::StatusOr<std::optional<std::string>> server_read =
      (*server_session)->Read();
  ASSERT_THAT(server_read, IsOk());
  ASSERT_THAT(*server_read, Eq(std::nullopt));
}

TEST(ClientServerSessionTest, ClientEncryptServerDecrypt) {
  auto client_session = ClientSession::Create();
  auto server_session = ServerSession::Create();

  DoHandshake(**client_session, **server_session);

  std::string request_text = "Hello Server";

  ASSERT_THAT((*client_session)->Write(request_text), IsOk());
  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOk());
  ASSERT_THAT(*request, Ne(std::nullopt));

  ASSERT_THAT((*server_session)->PutIncomingMessage(**request), IsOk());
  absl::StatusOr<std::optional<std::string>> received_request =
      (*server_session)->Read();
  ASSERT_THAT(received_request, IsOk());
  ASSERT_THAT(*received_request, Ne(std::nullopt));

  EXPECT_THAT(**received_request, Eq(request_text));
}

TEST(ClientServerSessionTest, ServerEncryptClientDecrypt) {
  auto client_session = ClientSession::Create();
  auto server_session = ServerSession::Create();

  DoHandshake(**client_session, **server_session);

  std::string response_text = "Hello Server";

  ASSERT_THAT((*server_session)->Write(response_text), IsOk());
  absl::StatusOr<std::optional<SessionResponse>> response =
      (*server_session)->GetOutgoingMessage();
  ASSERT_THAT(response, IsOk());
  ASSERT_THAT(*response, Ne(std::nullopt));

  ASSERT_THAT((*client_session)->PutIncomingMessage(**response), IsOk());
  absl::StatusOr<std::optional<std::string>> received_response =
      (*client_session)->Read();
  ASSERT_THAT(received_response, IsOk());
  ASSERT_THAT(*received_response, Ne(std::nullopt));

  EXPECT_THAT(**received_response, Eq(response_text));
}

}  // namespace
}  // namespace oak::session

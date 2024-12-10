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

#include "cc/server/session_server.h"

#include "absl/status/status_matchers.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::server {
namespace {

using ::absl_testing::IsOk;
using ::testing::Eq;
using ::testing::Ne;
using ::testing::Optional;

class TestTransport : public OakSessionServer::Channel::Transport {
 public:
  TestTransport(std::unique_ptr<session::ClientSession> client_session)
      : client_session_(std::move(client_session)) {}
  absl::Status Send(const session::v1::SessionResponse& request) override {
    return client_session_->PutIncomingMessage(request);
  }
  absl::StatusOr<session::v1::SessionRequest> Receive() override {
    absl::StatusOr<std::optional<session::v1::SessionRequest>> msg =
        client_session_->GetOutgoingMessage();
    if (!msg.ok()) {
      return msg.status();
    }
    if (*msg == std::nullopt) {
      return absl::FailedPreconditionError("expected outgoing client message");
    }
    return **msg;
  }

 private:
  std::unique_ptr<session::ClientSession> client_session_;
};

TEST(OakSessionServerTest, CreateSuccessFullyHandshakes) {
  auto client_session = session::ClientSession::Create();
  ASSERT_THAT(client_session, IsOk());
  auto _ = OakSessionServer().NewChannel(
      std::make_unique<TestTransport>(std::move(*client_session)));
}

TEST(OakSessionServerTest, CreatedSessionCanSend) {
  auto client_session = session::ClientSession::Create();
  // Hold a pointer for testing behavior below.
  session::ClientSession* client_session_ptr = client_session->get();
  ASSERT_THAT(client_session, IsOk());
  auto channel = OakSessionServer().NewChannel(
      std::make_unique<TestTransport>(std::move(*client_session)));

  std::string test_send_msg = "Testing Send";
  ASSERT_THAT((*channel)->Send(test_send_msg), IsOk());
  absl::StatusOr<std::optional<std::string>> test_send_read_back =
      client_session_ptr->Read();
  EXPECT_THAT(test_send_read_back, IsOk());
  EXPECT_THAT(*test_send_read_back, Optional(Eq(test_send_msg)));
}

TEST(OakSessionServerTest, CreatedSessionCanReceive) {
  auto client_session = session::ClientSession::Create();
  // Hold a pointer for testing behavior below.
  session::ClientSession* client_session_ptr = client_session->get();
  ASSERT_THAT(client_session, IsOk());
  auto channel = OakSessionServer().NewChannel(
      std::make_unique<TestTransport>(std::move(*client_session)));

  std::string test_recv_msg = "Testing Receive";
  ASSERT_THAT(client_session_ptr->Write(test_recv_msg), IsOk());

  absl::StatusOr<std::string> server_read = (*channel)->Receive();
  EXPECT_THAT(server_read, IsOk());
  EXPECT_THAT(*server_read, Eq(test_recv_msg));
}
}  // namespace
}  // namespace oak::server

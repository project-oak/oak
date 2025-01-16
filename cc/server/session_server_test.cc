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

#include <memory>
#include <optional>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::server {
namespace {

using ::absl_testing::IsOk;
using ::testing::Eq;
using ::testing::Ne;

class TestTransport : public OakSessionServer::Channel::Transport {
 public:
  TestTransport(std::unique_ptr<session::ClientSession> client_session)
      : client_session_(std::move(client_session)) {}
  absl::Status Send(session::v1::SessionResponse&& request) override {
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

session::SessionConfig* TestSessionConfig() {
  return session::SessionConfigBuilder(session::AttestationType::kUnattested,
                                       session::HandshakeType::kNoiseNN)
      .Build();
}

TEST(OakSessionServerTest, CreateSuccessFullyHandshakes) {
  auto client_session = session::ClientSession::Create(TestSessionConfig());
  ASSERT_THAT(client_session, IsOk());
  auto channel = OakSessionServer(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*client_session)));
  ASSERT_THAT(channel, IsOk());
}

TEST(OakSessionServerTest, SecondCreateSuccessFullyHandshakes) {
  auto server = OakSessionServer(TestSessionConfig);

  auto client_session = session::ClientSession::Create(TestSessionConfig());
  ASSERT_THAT(client_session, IsOk());
  auto channel = server.NewChannel(
      std::make_unique<TestTransport>(std::move(*client_session)));
  ASSERT_THAT(channel, IsOk());

  auto client_session2 = session::ClientSession::Create(TestSessionConfig());
  ASSERT_THAT(client_session2, IsOk());
  auto channel2 = server.NewChannel(
      std::make_unique<TestTransport>(std::move(*client_session2)));
  ASSERT_THAT(channel2, IsOk());
}

TEST(OakSessionServerTest, CreatedSessionCanSend) {
  auto client_session = session::ClientSession::Create(TestSessionConfig());
  // Hold a pointer for testing behavior below.
  session::ClientSession* client_session_ptr = client_session->get();
  ASSERT_THAT(client_session, IsOk());
  auto channel = OakSessionServer(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*client_session)));

  std::string test_send_msg = "Testing Send";
  ASSERT_THAT((*channel)->Send(test_send_msg), IsOk());
  absl::StatusOr<std::optional<session::v1::PlaintextMessage>>
      test_send_read_back = client_session_ptr->Read();
  EXPECT_THAT(test_send_read_back, IsOk());
  EXPECT_THAT(*test_send_read_back, Ne(std::nullopt));
  EXPECT_THAT((**test_send_read_back).plaintext(), Eq(test_send_msg));
}

TEST(OakSessionServerTest, CreatedSessionCanReceive) {
  auto client_session = session::ClientSession::Create(TestSessionConfig());
  // Hold a pointer for testing behavior below.
  session::ClientSession* client_session_ptr = client_session->get();
  ASSERT_THAT(client_session, IsOk());
  auto channel = OakSessionServer(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*client_session)));

  session::v1::PlaintextMessage test_recv_plaintext_msg;
  test_recv_plaintext_msg.set_plaintext("Testing Receive");
  ASSERT_THAT(client_session_ptr->Write(test_recv_plaintext_msg), IsOk());

  absl::StatusOr<std::string> server_read = (*channel)->Receive();
  EXPECT_THAT(server_read, IsOk());
  EXPECT_THAT(*server_read, Eq(test_recv_plaintext_msg.plaintext()));
}
}  // namespace
}  // namespace oak::server

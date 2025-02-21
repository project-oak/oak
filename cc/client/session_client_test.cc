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

#include "cc/client/session_client.h"

#include <memory>

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/status/status_matchers.h"
#include "absl/synchronization/mutex.h"
#include "cc/ffi/rust_bytes.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::client {
namespace {

using ::absl_testing::IsOk;
using ::absl_testing::IsOkAndHolds;
using ::absl_testing::StatusIs;
using ::testing::Eq;
using ::testing::Ne;
using ::testing::Optional;

class TestTransport : public OakSessionClient::Channel::Transport {
 public:
  TestTransport(std::unique_ptr<session::ServerSession> server_session)
      : server_session_(std::move(server_session)) {}
  absl::Status Send(session::v1::SessionRequest&& request) override {
    absl::MutexLock lock(&mtx_);
    if (half_closed_) {
      return absl::InternalError("Already half-closed.");
    }
    return server_session_->PutIncomingMessage(request);
  }
  absl::StatusOr<session::v1::SessionResponse> Receive() override {
    absl::StatusOr<std::optional<session::v1::SessionResponse>> msg =
        server_session_->GetOutgoingMessage();
    if (!msg.ok()) {
      return msg.status();
    }
    if (*msg == std::nullopt) {
      return absl::FailedPreconditionError("expected outgoing server message");
    }
    return **msg;
  }

  void HalfClose() override {
    absl::MutexLock lock(&mtx_);
    // TODO: zhumazhenis - half-close in server_session_ too if supports.
    half_closed_ = true;
  }

 private:
  std::unique_ptr<session::ServerSession> server_session_;
  absl::Mutex mtx_;
  bool half_closed_ ABSL_GUARDED_BY(mtx_) = false;
};

session::SessionConfig* TestSessionConfig() {
  return session::SessionConfigBuilder(session::AttestationType::kUnattested,
                                       session::HandshakeType::kNoiseNN)
      .Build();
}

TEST(OakSessionClientTest, CreateSuccessFullyHandshakes) {
  auto server_session = session::ServerSession::Create(TestSessionConfig());
  ASSERT_THAT(server_session, IsOk());
  auto channel = OakSessionClient(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*server_session)));
  EXPECT_THAT(channel, IsOk());
}

TEST(OakSessionClientTest, CreateSecondClientSuccessFullyHandshakes) {
  auto server_session = session::ServerSession::Create(TestSessionConfig());
  ASSERT_THAT(server_session, IsOk());
  auto client = OakSessionClient(TestSessionConfig);

  auto channel = client.NewChannel(
      std::make_unique<TestTransport>(std::move(*server_session)));
  EXPECT_THAT(channel, IsOk());

  auto server_session2 = session::ServerSession::Create(TestSessionConfig());
  auto channel2 = client.NewChannel(
      std::make_unique<TestTransport>(std::move(*server_session2)));
  EXPECT_THAT(channel2, IsOk());
}

TEST(OakSessionClientTest, CreatedSessionCanSend) {
  auto server_session = session::ServerSession::Create(TestSessionConfig());
  // Hold a pointer for testing behavior below.
  session::ServerSession* server_session_ptr = server_session->get();
  ASSERT_THAT(server_session, IsOk());
  auto channel = OakSessionClient(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*server_session)));

  std::string test_send_msg = "Testing Send";
  ASSERT_THAT((*channel)->Send(test_send_msg), IsOk());
  absl::StatusOr<std::optional<ffi::RustBytes>> test_send_read_back =
      server_session_ptr->ReadToRustBytes();
  EXPECT_THAT(test_send_read_back, IsOkAndHolds(Optional(Eq(test_send_msg))));
}

TEST(OakSessionClientTest, HalfClosedSessionFailsToSend) {
  auto server_session = session::ServerSession::Create(TestSessionConfig());
  ASSERT_THAT(server_session, IsOk());
  auto channel = OakSessionClient(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*server_session)));

  (*channel)->HalfClose();

  std::string test_send_msg = "Testing Send";
  EXPECT_THAT((*channel)->Send(test_send_msg),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(OakSessionClientTest, CreatedSessionCanReceive) {
  auto server_session = session::ServerSession::Create(TestSessionConfig());
  // Hold a pointer for testing behavior below.
  session::ServerSession* server_session_ptr = server_session->get();
  ASSERT_THAT(server_session, IsOk());
  auto channel = OakSessionClient(TestSessionConfig)
                     .NewChannel(std::make_unique<TestTransport>(
                         std::move(*server_session)));

  std::string test_recv_msg = "Testing Receive";
  ASSERT_THAT(server_session_ptr->Write(test_recv_msg), IsOk());

  absl::StatusOr<std::string> server_read = (*channel)->Receive();
  EXPECT_THAT(server_read, IsOkAndHolds(test_recv_msg));
}
}  // namespace
}  // namespace oak::client

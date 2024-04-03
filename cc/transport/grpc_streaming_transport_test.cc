/*
 * Copyright 2023 The Project Oak Authors
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

#include "cc/transport/grpc_streaming_transport.h"

#include <chrono>
#include <thread>

#include "absl/log/absl_check.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "grpcpp/server_builder.h"
#include "grpcpp/support/time.h"
#include "gtest/gtest.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"
#include "proto/session/service_streaming.grpc.pb.h"
#include "proto/session/service_streaming.pb.h"

using oak::crypto::v1::EncryptedRequest;
using oak::crypto::v1::EncryptedResponse;
using oak::session::v1::EndorsedEvidence;
using oak::session::v1::RequestWrapper;
using oak::session::v1::ResponseWrapper;
using oak::transport::GrpcStreamingTransport;
using ::testing::_;
using ServerStream =
    ::grpc::ServerReaderWriter<ResponseWrapper, RequestWrapper>;
using ClientStream =
    ::grpc::ClientReaderWriterInterface<RequestWrapper, ResponseWrapper>;

class MockServiceStreaming
    : public ::oak::session::v1::StreamingSession::Service {
 public:
  MOCK_METHOD(grpc::Status, Stream, (grpc::ServerContext*, (ServerStream*)),
              (override));
};
class GrpcStreamingTransportTest : public ::testing::Test {
 protected:
  ::grpc::ClientContext context_;
  std::unique_ptr<grpc::Server> server_;
  std::shared_ptr<grpc::Channel> channel_;
  std::unique_ptr<oak::session::v1::StreamingSession::StubInterface> stub_;
  MockServiceStreaming mock_service_;

  void SetUp() override {
    grpc::ServerBuilder server_builder;
    server_builder.RegisterService(&mock_service_);
    server_ = server_builder.BuildAndStart();
    channel_ = server_->InProcessChannel({});
    stub_ = oak::session::v1::StreamingSession::NewStub(channel_);

    context_.set_deadline(gpr_time_from_seconds(10, GPR_TIMESPAN));
  }

  void TearDown() override {
    server_->Shutdown();
    server_->Wait();
  }
};

TEST_F(GrpcStreamingTransportTest, InvokePropagatesSendError) {
  GrpcStreamingTransport transport(stub_->Stream(&context_));

  EXPECT_CALL(mock_service_, Stream(_, _))
      .WillOnce([](grpc::ServerContext*, ServerStream* stream) {
        return grpc::Status(grpc::StatusCode::FAILED_PRECONDITION,
                            "fake error");
      });

  EncryptedRequest request;
  absl::StatusOr<oak::crypto::v1::EncryptedResponse> response =
      transport.Invoke(request);
  ASSERT_EQ(response.status(),
            absl::Status(absl::StatusCode::kFailedPrecondition,
                         "while writing request: fake error"));
}

TEST_F(GrpcStreamingTransportTest, GetEndorsedEvidencePropagatesSendError) {
  GrpcStreamingTransport transport(stub_->Stream(&context_));

  EXPECT_CALL(mock_service_, Stream(_, _))
      .WillOnce([](grpc::ServerContext*, ServerStream* stream) {
        return grpc::Status(grpc::StatusCode::FAILED_PRECONDITION,
                            "fake error");
      });

  absl::StatusOr<EndorsedEvidence> response = transport.GetEndorsedEvidence();
  ASSERT_EQ(response.status(),
            absl::Status(absl::StatusCode::kFailedPrecondition,
                         "while writing request: fake error"));
}

TEST_F(GrpcStreamingTransportTest, InvokePropagatesWeirdError) {
  GrpcStreamingTransport transport(stub_->Stream(&context_));

  EXPECT_CALL(mock_service_, Stream(_, _))
      .WillOnce([](grpc::ServerContext*, ServerStream* stream) {
        return grpc::Status::OK;
      });

  EncryptedRequest request;
  absl::StatusOr<oak::crypto::v1::EncryptedResponse> response =
      transport.Invoke(request);

  ASSERT_EQ(response.status().code(), absl::StatusCode::kInternal);
  EXPECT_THAT(response.status().message(),
              testing::StartsWith("failed to read request"));
}

TEST_F(GrpcStreamingTransportTest, GetEndorsedEvidencePropagatesWeirdError) {
  ::grpc::ClientContext context;
  GrpcStreamingTransport transport(stub_->Stream(&context));

  EXPECT_CALL(mock_service_, Stream(_, _))
      .WillOnce([](grpc::ServerContext*, ServerStream* stream) {
        return grpc::Status::OK;
      });

  absl::StatusOr<EndorsedEvidence> response = transport.GetEndorsedEvidence();

  ASSERT_EQ(response.status().code(), absl::StatusCode::kInternal);
  EXPECT_THAT(response.status().message(),
              testing::StartsWith("failed to read request"));
}

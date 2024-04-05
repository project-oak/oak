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

#include "cc/transport/grpc_unary_transport.h"

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/messages.pb.h"
#include "proto/session/service_unary.pb.h"
#include "proto/session/service_unary_mock.grpc.pb.h"

namespace oak::transport {
namespace {

using ::oak::crypto::v1::AeadEncryptedMessage;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::session::v1::GetEndorsedEvidenceRequest;
using ::oak::session::v1::GetEndorsedEvidenceResponse;
using ::oak::session::v1::InvokeRequest;
using ::oak::session::v1::InvokeResponse;
using ::oak::session::v1::MockUnarySessionStub;

using ::testing::_;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::StrEq;

TEST(StubbyUnaryTransportTest, KeyRetrievedAndInvokeCalledSuccess) {
  auto mock_stub = std::make_unique<MockUnarySessionStub>();

  // Test the get endorsed evidence method.
  GetEndorsedEvidenceRequest empty_request;
  GetEndorsedEvidenceResponse evidence_response;
  std::string application_key = "001";
  *evidence_response.mutable_endorsed_evidence()
       ->mutable_evidence()
       ->mutable_application_keys()
       ->mutable_encryption_public_key_certificate() = application_key;

  EXPECT_CALL(*mock_stub, GetEndorsedEvidence(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(evidence_response), Return(grpc::Status::OK)));

  GrpcUnaryTransport<MockUnarySessionStub> unary_transport(mock_stub.get());

  auto actual_endorsed_evidence = unary_transport.GetEndorsedEvidence();
  ASSERT_TRUE(actual_endorsed_evidence.ok());
  EXPECT_THAT(actual_endorsed_evidence->evidence()
                  .application_keys()
                  .encryption_public_key_certificate(),
              StrEq(application_key));

  // Now we test the invoke method.

  const std::string request_ciphertext = "Some encrypted request.";
  AeadEncryptedMessage request_aead_encrypted_message;
  request_aead_encrypted_message.set_ciphertext(request_ciphertext);
  EncryptedRequest encrypted_request;
  *encrypted_request.mutable_encrypted_message() =
      request_aead_encrypted_message;
  InvokeRequest invoke_request;
  *invoke_request.mutable_encrypted_request() = encrypted_request;

  const std::string response_ciphertext = "Some encrypted response.";
  AeadEncryptedMessage response_aead_encrypted_message;
  response_aead_encrypted_message.set_ciphertext(response_ciphertext);
  EncryptedResponse encrypted_response;
  *encrypted_response.mutable_encrypted_message() =
      response_aead_encrypted_message;
  InvokeResponse invoke_response;
  *invoke_response.mutable_encrypted_response() = encrypted_response;

  EXPECT_CALL(*mock_stub, Invoke(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(invoke_response), Return(::grpc::Status::OK)));

  auto actual_encrypted_response = unary_transport.Invoke(encrypted_request);
  ASSERT_TRUE(actual_encrypted_response.ok());

  EXPECT_THAT(actual_encrypted_response->encrypted_message().ciphertext(),
              StrEq(response_ciphertext));
}

}  // namespace
}  // namespace oak::transport

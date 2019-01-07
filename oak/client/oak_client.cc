/*
 * Copyright 2018 The Project Oak Authors
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

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/identity/init.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"
#include "include/grpcpp/grpcpp.h"

#include "oak/proto/oak_server.grpc.pb.h"

#include <fstream>

DEFINE_string(server_address, "127.0.0.1:8888", "Address of the server to connect to");
DEFINE_string(business_logic, "", "File containing the compiled Wasm business logic");
DEFINE_string(expression, "", "The top-level Wasm expression to evaluate");

class OakClient {
 public:
  OakClient(const std::shared_ptr<::grpc::ChannelInterface>& channel)
      : stub_(::oak::OakServer::NewStub(channel, ::grpc::StubOptions())) {
    {
      ::grpc::ClientContext context;

      ::oak::InitiateComputationRequest request;
      ::oak::InitiateComputationResponse response;

      std::ifstream t(FLAGS_business_logic, std::ifstream::in);
      if (!t.is_open()) {
        LOG(QFATAL) << "Could not open file " << FLAGS_business_logic;
      }
      std::stringstream buffer;
      buffer << t.rdbuf();
      LOG(INFO) << "Module size: " << buffer.str().size();

      request.set_business_logic(buffer.str());

      ::grpc::Status status = this->stub_->InitiateComputation(&context, request, &response);
      if (!status.ok()) {
        LOG(QFATAL) << "Failed: " << status.error_message();
      }

      LOG(INFO) << "response: " << response.DebugString();
    }

    {
      ::grpc::ClientContext context;

      ::oak::SetChannelDataRequest request;
      ::oak::SetChannelDataResponse response;

      request.set_channel_id(0);
      request.set_data("123");
      ::grpc::Status status = this->stub_->SetChannelData(&context, request, &response);
      if (!status.ok()) {
        LOG(QFATAL) << "Failed: " << status.error_message();
      }
    }
  }

 private:
  std::unique_ptr<::oak::OakServer::Stub> stub_;
};

int main(int argc, char** argv) {
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  if (FLAGS_server_address.empty()) {
    LOG(QFATAL) << "Must supply a non-empty address with --server_address";
  }

  if (FLAGS_business_logic.empty()) {
    LOG(QFATAL) << "Must supply a non-empty business logic with --business_logic";
  }

  if (FLAGS_expression.empty()) {
    LOG(QFATAL) << "Must supply a non-empty expression logic with --expression";
  }

  std::vector<::asylo::EnclaveAssertionAuthorityConfig> configs;
  ::asylo::Status status =
      ::asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
  if (!status.ok()) {
    LOG(QFATAL) << "Could not initialise assertion authorities";
  }

  LOG(INFO) << "start";

  OakClient client(::grpc::CreateChannel(
      FLAGS_server_address,
      ::asylo::EnclaveChannelCredentials(::asylo::BidirectionalNullCredentialsOptions())));
}

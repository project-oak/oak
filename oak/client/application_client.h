/*
 * Copyright 2019 The Project Oak Authors
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

#ifndef OAK_CLIENT_APPLICATION_CLIENT_H_
#define OAK_CLIENT_APPLICATION_CLIENT_H_

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/init.h"
#include "asylo/util/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/policy_metadata.h"
#include "oak/proto/application.grpc.pb.h"

namespace oak {

// A client connected to a previously created Oak Application.
//
// It allows invoking the Oak Application as specified by the Oak Application policies.
//
// TODO: Verify remote attestations.
// TODO: Make this class take ownership of the gRPC channel (e.g. via a unique_ptr), and force
// clients to instantiate gRPC stubs via it, or parametrize this class with the type of the stub to
// instantiate.
class ApplicationClient {
 public:
  ApplicationClient(const std::shared_ptr<grpc::ChannelInterface>& channel)
      : stub_(Application::NewStub(channel, grpc::StubOptions())) {
    InitializeAssertionAuthorities();
  }

  GetAttestationResponse GetAttestation() {
    grpc::ClientContext context;
    GetAttestationRequest request;
    GetAttestationResponse response;
    auto status = stub_->GetAttestation(&context, request, &response);
    if (!status.ok()) {
      LOG(QFATAL) << "Could not get attestation: " << status.error_code() << ": "
                  << status.error_message();
    }
    return response;
  }

  // Returns a grpc Channel connecting to the specified address, initialised with:
  // - Asylo channel credentials, possibly attesting the entire channel to the remote enclave
  // - Oak Policy call credentials, possibly attaching a specific Oak Policy to each call
  // See https://grpc.io/docs/guides/auth/.
  static std::shared_ptr<grpc::Channel> CreateChannel(std::string addr) {
    auto channel_credentials =
        asylo::EnclaveChannelCredentials(asylo::BidirectionalNullCredentialsOptions());
    auto call_credentials =
        grpc::MetadataCredentialsFromPlugin(absl::make_unique<PolicyMetadata>());
    auto composite_credentials =
        grpc::CompositeChannelCredentials(channel_credentials, call_credentials);
    return grpc::CreateChannel(addr, composite_credentials);
  }

  static asylo::EnclaveAssertionAuthorityConfig GetNullAssertionAuthorityConfig() {
    asylo::EnclaveAssertionAuthorityConfig test_config;
    asylo::SetNullAssertionDescription(test_config.mutable_description());
    return test_config;
  }

  // This method sets up the necessary global state for Asylo to be able to validate authorities
  // (e.g. root CAs, remote attestation endpoints, etc.).
  static void InitializeAssertionAuthorities() {
    LOG(INFO) << "Initializing assertion authorities";

    // TODO: Provide a list of non-null Assertion Authorities when available.
    std::vector<asylo::EnclaveAssertionAuthorityConfig> configs = {
        GetNullAssertionAuthorityConfig(),
    };

    asylo::Status status =
        asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
    if (!status.ok()) {
      LOG(QFATAL) << "Could not initialize assertion authorities";
    }

    LOG(INFO) << "Assertion authorities initialized";
  }

  std::unique_ptr<Application::Stub> stub_;
};

}  // namespace oak

#endif  // OAK_CLIENT_APPLICATION_CLIENT_H_

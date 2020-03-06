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
#include "include/grpcpp/grpcpp.h"
#include "oak/client/authorization_bearer_token_metadata.h"
#include "oak/client/policy_metadata.h"
#include "oak/common/hmac.h"
#include "oak/common/logging.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/policy.h"
#include "oak/proto/policy.pb.h"

namespace oak {

constexpr size_t kPerChannelNonceSizeBytes = 32;

namespace {
const std::string kBearerTokenHmacData{"oak-grpc-bearer-token-1"};
}  // namespace

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
  ApplicationClient(const std::shared_ptr<grpc::ChannelInterface>& channel) {
    InitializeAssertionAuthorities();
  }

  // Creates gRPC channel credentials by using the provided (secret) token to authenticate, and the
  // derived (public) token HMAC to set a corresponding label on any data sent over the call.
  static std::shared_ptr<grpc::CallCredentials> authorization_bearer_token_call_credentials(
      const std::string& authorization_bearer_token) {
    std::string authorization_bearer_token_hmac =
        oak::utils::hmac_sha256(authorization_bearer_token, kBearerTokenHmacData).ValueOrDie();

    return grpc::CompositeCallCredentials(
        grpc::MetadataCredentialsFromPlugin(
            absl::make_unique<AuthorizationBearerTokenMetadata>(authorization_bearer_token)),
        grpc::MetadataCredentialsFromPlugin(absl::make_unique<PolicyMetadata>(
            AuthorizationBearerTokenPolicy(authorization_bearer_token_hmac))));
  }

  // Generates a fresh nonce to use as authorization bearer token, and uses that to authenticate and
  // also set a corresponding label on any data sent over this call that allows only this instance
  // of the call to be able to retrieve it.
  //
  // For instance, a client may interact with a server and send some data, and then later on
  // retrieve the data via a different call over the same channel.
  //
  // Note that the generated token is not directly accessible outside of this method: if the channel
  // is closed (either intentionally or accidentally) then the previously sent data will not be
  // accessible any more, since a new channel will be required, which will be associated with a
  // different token.
  //
  // TODO: Consider introducing a server-side garbage collection mechanism so that inaccessible data
  // may be deleted. If this is not feasible, perhaps it may be based on access time only, or based
  // on additional metadata or specific time-related policies.
  static std::shared_ptr<grpc::CallCredentials>
  private_authorization_bearer_token_call_credentials() {
    NonceGenerator<kPerChannelNonceSizeBytes> nonce_generator;
    std::string channel_authorization_bearer_token = NonceToBytes(nonce_generator.NextNonce());

    return authorization_bearer_token_call_credentials(channel_authorization_bearer_token);
  }

  // Returns a grpc Channel connecting to the specified address initialised with the following
  // composite channel credentials:
  // - Asylo channel credentials, possibly attesting the entire channel to the remote enclave
  // - Oak Policy call credentials, possibly attaching a specific Oak Policy to each call
  //
  // Note that composite channel credentials are really channel credentials, plus a generator object
  // that modifies metadata for each call, and in this case it happens to always attach the same
  // metadata to each outgoing call.
  //
  // See https://grpc.io/docs/guides/auth/.
  static std::shared_ptr<grpc::Channel> CreateChannel(
      std::string addr, std::shared_ptr<grpc::CallCredentials> call_credentials) {
    auto channel_credentials =
        asylo::EnclaveChannelCredentials(asylo::BidirectionalNullCredentialsOptions());

    auto composite_credentials =
        grpc::CompositeChannelCredentials(channel_credentials, call_credentials);

    return grpc::CreateChannel(addr, composite_credentials);
  }

  // Returns a gRPC Channel initialized with a private authorization bearer token.
  //
  // See `private_authorization_bearer_token_call_credentials`.
  static std::shared_ptr<grpc::Channel> CreateChannel(std::string addr) {
    return CreateChannel(addr, private_authorization_bearer_token_call_credentials());
  }

  static asylo::EnclaveAssertionAuthorityConfig GetNullAssertionAuthorityConfig() {
    asylo::EnclaveAssertionAuthorityConfig test_config;
    asylo::SetNullAssertionDescription(test_config.mutable_description());
    return test_config;
  }

  // This method sets up the necessary global state for Asylo to be able to validate authorities
  // (e.g. root CAs, remote attestation endpoints, etc.).
  static void InitializeAssertionAuthorities() {
    OAK_LOG(INFO) << "Initializing assertion authorities";

    // TODO: Provide a list of non-null Assertion Authorities when available.
    std::vector<asylo::EnclaveAssertionAuthorityConfig> configs = {
        GetNullAssertionAuthorityConfig(),
    };

    asylo::Status status =
        asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
    if (!status.ok()) {
      OAK_LOG(QFATAL) << "Could not initialize assertion authorities";
    }

    OAK_LOG(INFO) << "Assertion authorities initialized";
  }
};

}  // namespace oak

#endif  // OAK_CLIENT_APPLICATION_CLIENT_H_

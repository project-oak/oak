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

#include "oak/client/sgx_application_client.h"

#include <memory>
#include <string>
#include <vector>

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/enclave_credentials_options.h"
#include "asylo/grpc/auth/null_credentials_options.h"
// TODO: Uncomment when Asylo will release remote attestation.
//#include "asylo/grpc/auth/sgx_remote_credentials_options.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/enclave_assertion_authority_configs.h"
#include "asylo/identity/init.h"
#include "asylo/identity/sgx/sgx_identity_util.h"
#include "asylo/identity/util/sha256_hash.pb.h"
#include "asylo/util/logging.h"
#include "asylo/util/status.h"
#include "asylo/util/statusor.h"
#include "oak/client/authorization_bearer_token_metadata.h"
#include "oak/client/policy_metadata.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/policy.h"

using asylo::Status;
using asylo::StatusOr;

constexpr size_t kPerChannelNonceSizeBytes = 32;
// Debug MRSIGNER value derived from the SGX test key (will change after changing SVN and PRODID).
// https://github.com/google/asylo/blob/088ea3490dd4579655bd5b65b0e31fe18de7f6dd/asylo/distrib/sgx_x86_64/linux_sgx_2_6.patch#L5481
const char* kDebugMrSigner = "83d719e77deaca1470f6baf62a4d774303c899db69020f9c70ee1dfc08c7ce9e";
// Debug CPUSVN value.
// This value should be provided by EREPORT and it reflects the microcode update version.
const char* kDebugCpuSvn = "0000000000000000";

// Parses a hexademical hash string from `hash_string` into `Sha256HashProto` in `hash`.
// TODO: Use same function from Asylo, when it becomes public.
Status Sha256HashFromHexString(const std::string& hash_string, asylo::Sha256HashProto* hash) {
  if (hash_string.size() != 64) {
    return Status(asylo::error::GoogleError::INTERNAL,
                         "Hash string size is not 64: " + hash_string);
  }
  for (auto ch : hash_string) {
    if (std::isxdigit(ch) == 0) {
      return Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                           "Hash contains non-hexademical charachters: " + hash_string);
    }
  }
  hash->set_hash(absl::HexStringToBytes(hash_string));
  return Status::OkStatus();
}

namespace oak {

SgxApplicationClient::SgxApplicationClient(std::vector<std::string> mrenclave_strings) {
  // Initialize assertion authorities.
  this->InitializeAssertionAuthorities();

  // Initialize credentials.
  auto channel_credentials = this->CreateChannelCredentials(mrenclave_strings);
  auto call_credentials = this->CreateCallCredentials();
  this->credentials_ = grpc::CompositeChannelCredentials(channel_credentials, call_credentials);
}

std::shared_ptr<grpc::Channel> SgxApplicationClient::CreateChannel(std::string address) {
  return grpc::CreateChannel(address, this->credentials_);
}

asylo::EnclaveAssertionAuthorityConfig SgxApplicationClient::GetNullAssertionAuthorityConfig() {
  asylo::EnclaveAssertionAuthorityConfig test_config;
  asylo::SetNullAssertionDescription(test_config.mutable_description());
  return test_config;
}

void SgxApplicationClient::InitializeAssertionAuthorities() {
  LOG(INFO) << "Initializing assertion authorities";
  std::vector<asylo::EnclaveAssertionAuthorityConfig> configs = {
      GetNullAssertionAuthorityConfig(),
      // TODO: Provide SGX remote Assertion Authorities when available.
      // GetSgxRemoteAssertionAuthorityConfig()
  };

  auto status = asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
  if (!status.ok()) {
    LOG(QFATAL) << "Could not initialize assertion authorities: " << status;
  }
  LOG(INFO) << "Assertion authorities initialized";
}

// TODO: Add CPUSVN as a parameter.
StatusOr<asylo::EnclaveIdentityExpectation> SgxApplicationClient::CreateSgxIdentityExpectation(
    std::string& mrenclave_string) const {
  asylo::SgxIdentity sgx_identity;

  // Assign code identity.
  auto code_identity = sgx_identity.mutable_code_identity();
  auto status = Sha256HashFromHexString(mrenclave_string, code_identity->mutable_mrenclave());
  if (!status.ok()) {
    return status;
  }

  auto signer_assigned_identity = code_identity->mutable_signer_assigned_identity();
  status = Sha256HashFromHexString(kDebugMrSigner, signer_assigned_identity->mutable_mrsigner());
  if (!status.ok()) {
    return status;
  }
  // TODO: Consider assigning prodid and svn even without MRSIGNER.
  signer_assigned_identity->set_isvprodid(0);
  signer_assigned_identity->set_isvsvn(0);

  // TODO: Use Asylo misc attributes util when they become available.
  code_identity->set_miscselect(0);
  auto attributes = code_identity->mutable_attributes();
  attributes->set_flags(0);
  attributes->set_xfrm(0);

  // Assign machine configuration.
  auto machine_configuration = sgx_identity.mutable_machine_configuration();
  machine_configuration->mutable_cpu_svn()->set_value(kDebugCpuSvn);
  machine_configuration->set_sgx_type(asylo::sgx::SgxType::STANDARD);

  if (!asylo::IsValidSgxIdentity(sgx_identity)) {
    return Status(asylo::error::GoogleError::INTERNAL, "Invalid SGX identity");
  }

  // Generate expectation based on identity and an option mask.
  auto sgx_expectation = asylo::CreateSgxIdentityExpectation(
      sgx_identity, asylo::SgxIdentityMatchSpecOptions::STRICT_REMOTE);
  if (!sgx_expectation.ok()) {
    return sgx_expectation.status();
  }

  return asylo::SerializeSgxIdentityExpectation(sgx_expectation.ValueOrDie());
}

StatusOr<asylo::IdentityAclPredicate> SgxApplicationClient::CreateSgxIdentityAcl(
    std::vector<std::string>& mrenclave_strings) const {
  asylo::IdentityAclPredicate acl;
  auto acl_predicates = acl.mutable_acl_group();

  // Create a group of ACL values connected with `OR` statements.
  acl_predicates->set_type(asylo::IdentityAclGroup::OR);
  for (auto mrenclave_string : mrenclave_strings) {
    asylo::IdentityAclPredicate acl_predicate;

    // Add a predicate that verifies a single MRENCLAVE value.
    auto expectation = CreateSgxIdentityExpectation(mrenclave_string);
    if (expectation.ok()) {
      *acl_predicate.mutable_expectation() = expectation.ValueOrDie();
      *acl_predicates->add_predicates() = acl_predicate;
    } else {
      return expectation.status();
    }
  }
  return acl;
}

std::shared_ptr<grpc::ChannelCredentials> SgxApplicationClient::CreateChannelCredentials(
    std::vector<std::string>& mrenclave_strings) const {
  // TODO: Use remote attestation when it becomes available.
  auto credentials_options = asylo::BidirectionalNullCredentialsOptions();
  auto acl = this->CreateSgxIdentityAcl(mrenclave_strings);
  if (!acl.ok()) {
    LOG(QFATAL) << "CreateChannelCredentials failed: " << acl.status().error_message();
  }
  credentials_options.peer_acl = acl.ValueOrDie();
  return asylo::EnclaveChannelCredentials(credentials_options);
}

std::shared_ptr<grpc::CallCredentials> SgxApplicationClient::CreateCallCredentials() const {
  NonceGenerator<kPerChannelNonceSizeBytes> nonce_generator;
  auto channel_authorization_token_bytes = NonceToBytes(nonce_generator.NextNonce());
  auto call_credentials = grpc::CompositeCallCredentials(
      grpc::MetadataCredentialsFromPlugin(
          absl::make_unique<AuthorizationBearerTokenMetadata>(channel_authorization_token_bytes)),
      grpc::MetadataCredentialsFromPlugin(absl::make_unique<PolicyMetadata>(
          AuthorizationBearerTokenPolicy(channel_authorization_token_bytes))));
  return call_credentials;
}

}  // namespace oak

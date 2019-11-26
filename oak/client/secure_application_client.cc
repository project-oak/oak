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

#include "oak/client/secure_application_client.h"

#include <memory>
#include <string>
#include <vector>

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/enclave_credentials_options.h"
#include "asylo/grpc/auth/null_credentials_options.h"
//#include "asylo/grpc/auth/sgx_remote_credentials_options.h"
#include "asylo/identity/enclave_assertion_authority_configs.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/init.h"
#include "asylo/identity/sgx/sgx_identity_util.h"
#include "asylo/identity/util/sha256_hash_util.h"
#include "asylo/util/logging.h"
#include "oak/client/authorization_bearer_token_metadata.h"
#include "oak/client/policy_metadata.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/policy.h"

constexpr size_t kPerChannelNonceSizeBytes = 32;

namespace oak {

SecureApplicationClient::SecureApplicationClient(
    /*intel_public_key,*/
    std::vector<std::string> mrenclave_strings) {
  // Initialize assertion authorities
  this->InitializeAssertionAuthorities();

  // Initialize credentials
  auto channel_credentials = this->CreateChannelCredentials(mrenclave_strings);
  auto call_credentials = this->CreateCallCredentials();
  this->credentials_ =
      grpc::CompositeChannelCredentials(channel_credentials, call_credentials);
}

std::shared_ptr<grpc::Channel>
SecureApplicationClient::CreateChannel(std::string address) {
  return grpc::CreateChannel(address, this->credentials_);
}  
 
asylo::EnclaveAssertionAuthorityConfig
SecureApplicationClient::GetNullAssertionAuthorityConfig() {
  asylo::EnclaveAssertionAuthorityConfig test_config;
  asylo::SetNullAssertionDescription(test_config.mutable_description());
  return test_config;
}

void SecureApplicationClient::InitializeAssertionAuthorities() {
  LOG(INFO) << "Initializing assertion authorities";
  std::vector<asylo::EnclaveAssertionAuthorityConfig> configs = {
      GetNullAssertionAuthorityConfig(),
      // TODO: Provide SGX remote Assertion Authorities when available.
      //GetSgxRemoteAssertionAuthorityConfig()
  };

  auto status =
      asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
  if (!status.ok()) {
    LOG(QFATAL) << "Could not initialize assertion authorities";
  }
  LOG(INFO) << "Assertion authorities initialized";
}

// TODO: Add CPUSVN as a parameter.
asylo::EnclaveIdentityExpectation
SecureApplicationClient::CreateSgxIdentityExpectation(
    std::string& mrenclave_string, std::string mrsigner_string="") {
  asylo::SgxIdentity sgx_identity;
  asylo::SgxIdentityMatchSpec match_spec;

  // Assign code identity.
  auto code_identity = sgx_identity.mutable_code_identity();
  if (!asylo::Sha256HashFromHexString(mrenclave_string, code_identity->mutable_mrenclave())) {
    LOG(QFATAL) << "Bad MRENCLAVE";
  }

  if (!mrsigner_string.empty()) {
    auto signer_assigned_identity = code_identity->mutable_signer_assigned_identity();
    if (!asylo::Sha256HashFromHexString(
             mrsigner_string, signer_assigned_identity->mutable_mrsigner())) {
      LOG(QFATAL) << "Bad MRSIGNER";
    }
    // TODO: Consider assigning prodid and svn even without MRSIGNER.
    signer_assigned_identity->set_isvprodid(0);
    signer_assigned_identity->set_isvsvn(0);
  }
  // Currently asylo only supports EXINFO:
  // https://github.com/google/asylo/blob/088ea3490dd4579655bd5b65b0e31fe18de7f6dd/asylo/identity/sgx/secs_miscselect.h#L37-L41
  code_identity->set_miscselect(asylo::sgx::kMiscselectExinfoMask);
  if (!asylo::sgx::GetMustBeSetSecsAttributes(
           code_identity->mutable_attributes())) {
    LOG(QFATAL) << "Could not set attributes";
  }

  // Assign machine configuration.
  auto machine_configuration = sgx_identity.mutable_machine_configuration();
  machine_configuration->mutable_cpu_svn()->set_value("0000000000000000");
  // Currently asylo only supports SGX_TYPE_UNKNOWN and STANDARD:
  // https://github.com/google/asylo/blob/e8bff4742f0a3314ba553897ba00bb6042835ba3/asylo/identity/sgx/machine_configuration.proto#L32-L38
  machine_configuration->set_sgx_type(asylo::sgx::SgxType::STANDARD);

  // Assign code identity check mask
  auto code_identity_match_spec = match_spec.mutable_code_identity_match_spec();
  code_identity_match_spec->set_is_mrenclave_match_required(true);
  code_identity_match_spec->set_is_mrsigner_match_required(false);
  code_identity_match_spec->set_miscselect_match_mask(asylo::sgx::kMiscselectExinfoMask);
  auto status = asylo::sgx::SetDefaultSecsAttributesMask(
      code_identity_match_spec->mutable_attributes_match_mask()).ValueOrDie();

  // Assign machine configuration check mask.
  auto machine_config_match_spec = match_spec.mutable_machine_configuration_match_spec();
  machine_config_match_spec->set_is_cpu_svn_match_required(false);
  machine_config_match_spec->set_is_sgx_type_match_required(false);

  auto sgx_expectation =
      asylo::CreateSgxIdentityExpectation(sgx_identity, match_spec).ValueOrDie();
  return asylo::SerializeSgxIdentityExpectation(sgx_expectation).ValueOrDie();
}

asylo::IdentityAclPredicate
SecureApplicationClient::CreateSgxIdentityAcl(std::vector<std::string>& mrenclave_strings) {
  asylo::IdentityAclPredicate acl;
  auto acl_predicates = acl.mutable_acl_group();
  acl_predicates->set_type(asylo::IdentityAclGroup::OR);
  for (auto mrenclave_str : mrenclave_strings) {
    asylo::IdentityAclPredicate acl_predicate;
    *acl_predicate.mutable_expectation() = CreateSgxIdentityExpectation(mrenclave_str);
    *acl_predicates->add_predicates() = acl_predicate;
  }
  return acl;
}

std::shared_ptr<grpc::ChannelCredentials>
SecureApplicationClient::CreateChannelCredentials(
    std::vector<std::string>& mrenclave_strings) const {
  auto credentials_options = asylo::BidirectionalNullCredentialsOptions();
  // TODO: Use remote attestation when it will become available
  //auto credentials_options = 
  credentials_options.peer_acl = this->CreateSgxIdentityAcl(mrenclave_strings);
  return asylo::EnclaveChannelCredentials(credentials_opitons);
}

std::shared_ptr<grpc::CallCredentials>
SecureApplicationClient::CreateCallCredentials() const {
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

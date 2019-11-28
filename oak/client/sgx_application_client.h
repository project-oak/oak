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

#ifndef OAK_CLIENT_SGX_APPLICATION_CLIENT_H_
#define OAK_CLIENT_SGX_APPLICATION_CLIENT_H_

#include <memory>
#include <string>
#include <vector>

#include "asylo/grpc/auth/enclave_credentials_options.h"
#include "asylo/identity/enclave_assertion_authority_configs.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {

// A client connected to a previously created Oak Application.
//
// This client uses SGX remote attestation to validate the SGX platform and to
// check the correctness of the Oak enclave. The remote attestation only accepts
// an attestation in which the Oak enclave hash (MRENCLAVE value) is one of the
// hashes provided in `mrenclave_strings`.
// Current implementation uses debug parameters such as zero flags and an SGX test key:
// https://github.com/intel/linux-sgx/tree/master/psw/ae/ref_le/ref_keys
// TODO: Change to real values, when Asylo releases a client API.
class SgxApplicationClient {
 public:
  // Initializes an SGX application client.
  //
  // `mrenclave_strings` contains all valid Oak enclave hashes (hexadecimal strings).
  // TODO: Add parameter to specify Intel public key to use for verification.
  SgxApplicationClient(std::vector<std::string> mrenclave_strings);

  // Returns a secure grpc Channel connecting to the specified address.
  std::shared_ptr<grpc::Channel> CreateChannel(std::string address);

 private:
  // TODO: Use assertion helper from Asylo, when it becomes available.
  asylo::EnclaveAssertionAuthorityConfig GetNullAssertionAuthorityConfig();
  void InitializeAssertionAuthorities();

  // Create an ACL predicate that matches a single MRENCLAVE value with
  // corresponding SGX parameters:
  // https://asylo.dev/docs/guides/secure_grpc.html#server-acl
  asylo::StatusOr<asylo::EnclaveIdentityExpectation> CreateSgxIdentityExpectation(
      std::string& mrenclave_string) const;

  // Create an ACL that accepts any MRENCLAVE value from the `mrenclave_strings`.
  // An ACL consists of multiple predicates connected with `OR` statements.
  asylo::StatusOr<asylo::IdentityAclPredicate> CreateSgxIdentityAcl(
      std::vector<std::string>& mrenclave_strings) const;

  std::shared_ptr<grpc::ChannelCredentials> CreateChannelCredentials(
      std::vector<std::string>& mrenclave_strings) const;
  std::shared_ptr<grpc::CallCredentials> CreateCallCredentials() const;

  std::shared_ptr<grpc::ChannelCredentials> credentials_;
};

}  // namespace oak

#endif  // OAK_CLIENT_SGX_APPLICATION_CLIENT_H_

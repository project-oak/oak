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
#include "include/grpcpp/grpcpp.h"

namespace oak {

class SgxApplicationClient {
 public:
  SgxApplicationClient(
      /*TODO: intel_public_key,*/ std::vector<std::string> mrenclave_strings);

  std::shared_ptr<grpc::Channel> CreateChannel(std::string address);

 private:
  // TODO: Use assertion helper from asylo, when it becomes available.
  asylo::EnclaveAssertionAuthorityConfig GetNullAssertionAuthorityConfig();
  void InitializeAssertionAuthorities();

  asylo::EnclaveIdentityExpectation CreateSgxIdentityExpectation(
      std::string& mrenclave_string) const;
  asylo::IdentityAclPredicate CreateSgxIdentityAcl(
      std::vector<std::string>& mrenclave_strings) const;

  std::shared_ptr<grpc::ChannelCredentials> CreateChannelCredentials(
      std::vector<std::string>& mrenclave_strings) const;
  std::shared_ptr<grpc::CallCredentials> CreateCallCredentials() const;

  std::shared_ptr<grpc::ChannelCredentials> credentials_;
};

}  // namespace oak

#endif  // OAK_CLIENT_SGX_APPLICATION_CLIENT_H_

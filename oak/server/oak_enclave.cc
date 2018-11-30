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

#include "absl/memory/memory.h"

#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/grpc/util/enclave_server.h"
#include "asylo/trusted_application.h"
#include "asylo/util/status.h"

#include "oak/server/oak_server.h"

namespace asylo {

TrustedApplication *BuildTrustedApplication() {
  // return new
  // EnclaveServer(absl::make_unique<::oak::grpc_server::OakServer>(),
  // asylo::EnclaveServerCredentials(asylo::BidirectionalNullCredentialsOptions()));
  return new EnclaveServer(
      absl::make_unique<::oak::grpc_server::OakServer>(),
      ::asylo::EnclaveServerCredentials(::asylo::BidirectionalNullCredentialsOptions()));
}

}  // namespace asylo

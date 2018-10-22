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
  return new EnclaveServer(absl::make_unique<::oak::grpc_server::OakServer>(),
                           ::grpc::InsecureServerCredentials());
}

}  // namespace asylo

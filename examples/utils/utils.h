#include <fstream>

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/util/logging.h"
#include "grpcpp/security/credentials.h"

namespace oak {
namespace utils {

// Reads a binary file and returns its contents as a std::string.
std::string read_file(const std::string& module_path) {
  std::ifstream t(module_path, std::ifstream::in);
  if (!t.is_open()) {
    LOG(QFATAL) << "Could not open module " << module_path;
  }
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

std::shared_ptr<grpc::ChannelCredentials> get_credentials(bool insecure) {
  return insecure ? grpc::InsecureChannelCredentials()
                  : asylo::EnclaveChannelCredentials(asylo::BidirectionalNullCredentialsOptions());
}

}  // namespace utils
}  // namespace oak

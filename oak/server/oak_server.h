#include "oak/proto/oak_server.grpc.pb.h"

extern "C" {
#include "wac/wa.h"
}

namespace oak {
namespace grpc_server {

class OakServer final : public oak::OakServer::Service {
 public:
  OakServer();

 private:
  Module *module;

  ::grpc::Status InitiateComputation(::grpc::ServerContext *context,
                                     const ::oak::InitiateComputationRequest *request,
                                     ::oak::InitiateComputationResponse *response) override;
};

}  // namespace grpc_server
}  // namespace oak

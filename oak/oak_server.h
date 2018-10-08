#include "oak/oak_server.grpc.pb.h"

namespace oak {
namespace grpc_server {

class OakServer final : public oak::OakServer::Service {
  public:
    OakServer();

  private:
    ::grpc::Status InitiateComputation(::grpc::ServerContext *context,
                                      const ::oak::InitiateComputationRequest *request,
                                      ::oak::InitiateComputationResponse *response) override;
};

}
}

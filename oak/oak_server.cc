#include "oak/oak_server.h"

namespace oak {
namespace grpc_server {

  OakServer::OakServer() : Service() {}

  ::grpc::Status OakServer::InitiateComputation(::grpc::ServerContext *context,
                                               const ::oak::InitiateComputationRequest *request,
                                               ::oak::InitiateComputationResponse *response) {
  }

}
}

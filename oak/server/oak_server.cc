#include "asylo/util/logging.h"

#include "oak/server/oak_server.h"

namespace oak {
namespace grpc_server {

OakServer::OakServer() : Service() {}

::grpc::Status OakServer::InitiateComputation(::grpc::ServerContext *context,
                                              const ::oak::InitiateComputationRequest *request,
                                              ::oak::InitiateComputationResponse *response) {
  LOG(INFO) << "Initate Computation" << request;
  Options opts{
      .disable_memory_bounds = false,
      .mangle_table_index = false,
      .dlsym_trim_underscore = false,
  };
  load_module((uint8_t *)request->business_logic().c_str(), opts);
  return ::grpc::Status::OK;
}

}  // namespace grpc_server
}  // namespace oak

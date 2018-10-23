#include "asylo/util/logging.h"

#include "oak/server/oak_server.h"

namespace oak {
namespace grpc_server {

OakServer::OakServer() : Service() {}

::grpc::Status OakServer::InitiateComputation(::grpc::ServerContext *context,
                                              const ::oak::InitiateComputationRequest *request,
                                              ::oak::InitiateComputationResponse *response) {
  LOG(INFO) << "Initate Computation: " << request->DebugString();
  Options opts{
      .disable_memory_bounds = false,
      .mangle_table_index = false,
      .dlsym_trim_underscore = false,
  };

  Module *m = load_module((uint8_t *)request->business_logic().c_str(),
                          request->business_logic().size(), opts);

  int token_cnt = 3;
  char *tokens[] = {(char *)"mul", (char *)"11", (char *)"22"};

  int res = 0;
  fprintf(stderr, "Invoking function\n");
  // LOG(DEBUG) << "Invoking function";
  res = invoke(m, tokens[0], token_cnt - 1, tokens + 1);
  fprintf(stderr, "Function invoked\n");
  if (res) {
    // LOG(INFO) << "Result: " << value_repr(&m->stack[m->sp]);
    char *value = value_repr(&m->stack[m->sp]);
    fprintf(stderr, "value: %s", value);
    response->set_value(value);
  } else {
    // LOG(INFO) << "Error";
    fprintf(stderr, "error");
    response->set_value("error");
  }

  return ::grpc::Status::OK;
}

}  // namespace grpc_server
}  // namespace oak

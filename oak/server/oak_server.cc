#include "asylo/util/logging.h"

#include "oak/server/oak_server.h"

#include "src/binary-reader.h"
#include "src/error-formatter.h"
#include "src/error.h"
#include "src/interp/binary-reader-interp.h"
#include "src/interp/interp.h"

namespace oak {
namespace grpc_server {

// From https://github.com/WebAssembly/wabt/blob/master/src/tools/wasm-interp.cc .

static wabt::Features s_features;
static std::unique_ptr<wabt::FileStream> s_log_stream;
static std::unique_ptr<wabt::FileStream> s_stdout_stream;

static wabt::interp::Result PrintCallback(const wabt::interp::HostFunc* func,
                                          const wabt::interp::FuncSignature* sig,
                                          const wabt::interp::TypedValues& args,
                                          wabt::interp::TypedValues& results) {
  LOG(INFO) << "Called host";
  return wabt::interp::Result::Ok;
}

static wabt::Index UnknownFuncHandler(wabt::interp::Environment* env,
                                      wabt::interp::HostModule* host_module, wabt::string_view name,
                                      wabt::Index sig_index) {
  LOG(INFO) << "Unknown func export: " << name.to_string();
  std::pair<wabt::interp::HostFunc*, wabt::Index> pair =
      host_module->AppendFuncExport(name, sig_index, PrintCallback);
  return pair.second;
}

static void InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* go_module = env->AppendHostModule("go");
  go_module->on_unknown_func_export = UnknownFuncHandler;

  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");
  oak_module->on_unknown_func_export = UnknownFuncHandler;
}

static wabt::Result ReadModule(std::string module_bytes, wabt::interp::Environment* env,
                               wabt::Errors* errors, wabt::interp::DefinedModule** out_module) {
  LOG(INFO) << "Reading module";
  wabt::Result result;

  *out_module = nullptr;

  const bool kReadDebugNames = true;
  const bool kStopOnFirstError = true;
  const bool kFailOnCustomSectionError = true;
  wabt::ReadBinaryOptions options(s_features, s_log_stream.get(), kReadDebugNames,
                                  kStopOnFirstError, kFailOnCustomSectionError);

  LOG(INFO) << "xxx";
  result = wabt::ReadBinaryInterp(env, module_bytes.data(), module_bytes.size(), options, errors,
                                  out_module);
  LOG(INFO) << "yyy";

  if (Succeeded(result)) {
    // env->DisassembleModule(s_stdout_stream.get(), *out_module);
  }

  LOG(INFO) << "Read module";
  return result;
}

OakServer::OakServer() : Service() {}

::grpc::Status OakServer::InitiateComputation(::grpc::ServerContext* context,
                                              const ::oak::InitiateComputationRequest* request,
                                              ::oak::InitiateComputationResponse* response) {
  LOG(INFO) << "Initate Computation: " << request->DebugString();

  s_stdout_stream = wabt::FileStream::CreateStdout();

  wabt::Result result;
  wabt::interp::Environment env;
  InitEnvironment(&env);

  wabt::Errors errors;
  wabt::interp::DefinedModule* module = nullptr;
  result = ReadModule(request->business_logic(), &env, &errors, &module);
  if (wabt::Succeeded(result)) {
    LOG(INFO) << "Success";
  } else {
    LOG(INFO) << "Failure: " << result;
    LOG(INFO) << "Errors: " << wabt::FormatErrorsToString(errors, wabt::Location::Type::Binary);
  }

  // int token_cnt = 3;
  // char *tokens[] = {(char *)"mul", (char *)"11", (char *)"22"};

  // int res = 0;
  LOG(INFO) << "Invoking function";
  // res = invoke(m, tokens[0], token_cnt - 1, tokens + 1);
  LOG(INFO) << "Function invoked";
  // if (res) {
  // char *value = value_repr(&m->stack[m->sp]);
  // LOG(INFO) << "value: " << value;
  // response->set_value(value);
  //} else {
  // fprintf(stderr, "error");
  // LOG(INFO) << "error";
  // response->set_value("error");
  //}

  return ::grpc::Status::OK;
}

}  // namespace grpc_server
}  // namespace oak

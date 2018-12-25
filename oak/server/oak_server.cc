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

static std::unique_ptr<wabt::FileStream> s_log_stream = wabt::FileStream::CreateStdout();
static std::unique_ptr<wabt::FileStream> s_stdout_stream = wabt::FileStream::CreateStdout();

static wabt::interp::Result PrintCallback(const wabt::interp::HostFunc* func,
                                          const wabt::interp::FuncSignature* sig,
                                          const wabt::interp::TypedValues& args,
                                          wabt::interp::TypedValues& results) {
  LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
  for (auto const& arg : args) {
    LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
  }
  return wabt::interp::Result::Ok;
}

static std::vector<char> ReadMemory(wabt::interp::Environment* env, const uint32_t offset,
                                    const uint32_t size) {
  std::vector<char> data = env->GetMemory(0)->data;
  return std::vector<char>(data.cbegin() + offset, data.cbegin() + offset + size);
}

static std::string ReadString(wabt::interp::Environment* env, const uint32_t offset,
                              const uint32_t size) {
  std::vector<char> mem = ReadMemory(env, offset, size);
  return std::string(mem.cbegin(), mem.cend());
}

static void WriteMemory(wabt::interp::Environment* env, const uint32_t offset,
                        const std::vector<char> data) {
  std::copy(data.cbegin(), data.cend(), env->GetMemory(0)->data.begin() + offset);
}

static wabt::interp::HostFunc::Callback PrintString(wabt::interp::Environment* env) {
  return [env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
               const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    for (auto const& arg : args) {
      LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
    }
    LOG(INFO) << "Arg0-string: " << ReadString(env, args[0].get_i32(), args[1].get_i32());
    return wabt::interp::Result::Ok;
  };
}

static std::vector<char> i64Bytes(uint64_t val) {
  std::vector<char> vec(8);
  std::memcpy(&vec[0], &val, 8);
  return vec;
}

static wabt::interp::HostFunc::Callback OakGetTime(wabt::interp::Environment* env) {
  return [env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
               const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    auto now = std::chrono::system_clock::now();
    auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
    std::vector<char> ns_bytes = i64Bytes(ns);
    uint32_t p = args[0].get_i32();
    WriteMemory(env, p, ns_bytes);
    return wabt::interp::Result::Ok;
  };
}

static wabt::interp::HostFunc::Callback OakRead(wabt::interp::Environment* env) {
  return [env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
               const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    for (auto const& arg : args) {
      LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
    }
    std::string val = "XYZ";
    std::vector<char> val_bytes(val.cbegin(), val.cend());
    uint32_t p = args[1].get_i32();
    WriteMemory(env, p, val_bytes);
    return wabt::interp::Result::Ok;
  };
}

static wabt::Index UnknownFuncHandler(wabt::interp::Environment* env,
                                      wabt::interp::HostModule* host_module,
                                      const wabt::string_view name, const wabt::Index sig_index) {
  LOG(WARNING) << "Unknown func export: " << name.to_string() << " (sig=" << sig_index << ")";
  std::pair<wabt::interp::HostFunc*, wabt::Index> pair =
      host_module->AppendFuncExport(name, sig_index, PrintCallback);
  return pair.second;
}

static void InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* go_module = env->AppendHostModule("go");

  go_module->AppendFuncExport("debug", 1, PrintCallback);

  go_module->AppendFuncExport("runtime.wasmExit", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.wasmWrite", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.scheduleCallback", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.clearScheduledCallback", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.getRandomData", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.nanotime", 1, PrintCallback);
  go_module->AppendFuncExport("runtime.walltime", 1, PrintCallback);

  go_module->AppendFuncExport("syscall/js.stringVal", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueGet", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueSet", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueIndex", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueSetIndex", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueCall", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueNew", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueLength", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valuePrepareString", 1, PrintCallback);
  go_module->AppendFuncExport("syscall/js.valueLoadString", 1, PrintCallback);

  go_module->on_unknown_func_export = UnknownFuncHandler;

  // Rust.
  wabt::interp::HostModule* rust_module = env->AppendHostModule("__wbindgen_placeholder__");
  rust_module->on_unknown_func_export = UnknownFuncHandler;
  rust_module->AppendFuncExport(
      "__wbindgen_describe",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32},
                                  std::vector<wabt::Type>{}),
      PrintCallback);
  rust_module->AppendFuncExport(
      "__wbindgen_throw",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{}),
      PrintCallback);

  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");
  oak_module->AppendFuncExport(
      "print",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{}),
      PrintString(env));
  oak_module->AppendFuncExport(
      "get_time",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32},
                                  std::vector<wabt::Type>{}),
      OakGetTime(env));
  oak_module->AppendFuncExport(
      "read",
      wabt::interp::FuncSignature(
          std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32, wabt::Type::I32},
          std::vector<wabt::Type>{wabt::Type::I32}),
      OakRead(env));
}

static wabt::Result ReadModule(const std::string module_bytes, wabt::interp::Environment* env,
                               wabt::Errors* errors, wabt::interp::DefinedModule** out_module) {
  LOG(INFO) << "Reading module";
  wabt::Result result;

  *out_module = nullptr;

  wabt::Features s_features;
  const bool kReadDebugNames = true;
  const bool kStopOnFirstError = true;
  const bool kFailOnCustomSectionError = true;
  wabt::Stream* log_stream = nullptr;
  wabt::ReadBinaryOptions options(s_features, log_stream, kReadDebugNames, kStopOnFirstError,
                                  kFailOnCustomSectionError);

  result = wabt::ReadBinaryInterp(env, module_bytes.data(), module_bytes.size(), options, errors,
                                  out_module);

  if (Succeeded(result)) {
    // env->DisassembleModule(s_stdout_stream.get(), *out_module);
  }

  return result;
}

OakServer::OakServer() : Service() {}

::grpc::Status OakServer::InitiateComputation(::grpc::ServerContext* context,
                                              const ::oak::InitiateComputationRequest* request,
                                              ::oak::InitiateComputationResponse* response) {
  LOG(INFO) << "Initate Computation: " << request->DebugString();

  wabt::Result result;
  wabt::interp::Environment env;
  InitEnvironment(&env);
  LOG(INFO) << "Func count: " << env.GetFuncCount();

  wabt::Errors errors;
  wabt::interp::DefinedModule* module = nullptr;

  LOG(INFO) << "Reading module";
  result = ReadModule(request->business_logic(), &env, &errors, &module);
  if (wabt::Succeeded(result)) {
    LOG(INFO) << "Read module";
    wabt::interp::Thread::Options thread_options;

    // wabt::Stream* trace_stream = s_stdout_stream.get();
    wabt::Stream* trace_stream = nullptr;
    wabt::interp::Executor executor(&env, trace_stream, thread_options);
    LOG(INFO) << "Executing module";

    // module->start_func_index = 1;
    // wabt::interp::ExecResult exec_result = executor.RunStartFunction(module);

    wabt::interp::TypedValues args;

    // wabt::interp::TypedValue zero(wabt::Type::I32);
    // zero.set_i32(0);
    // args.push_back(zero);
    // args.push_back(zero);

    // wabt::interp::ExecResult exec_result = executor.RunExportByName(module, "run", args);
    wabt::interp::ExecResult exec_result = executor.RunExportByName(module, "oak_main", args);

    if (exec_result.result == wabt::interp::Result::Ok) {
      LOG(INFO) << "Executed module";
    } else {
      LOG(WARNING) << "Could not execute module";
      wabt::interp::WriteResult(s_stdout_stream.get(), "error", exec_result.result);
      // TODO: Print error.
    }
  } else {
    LOG(WARNING) << "Could not read module: " << result;
    LOG(WARNING) << "Errors: " << wabt::FormatErrorsToString(errors, wabt::Location::Type::Binary);
  }

  return ::grpc::Status::OK;
}

}  // namespace grpc_server
}  // namespace oak

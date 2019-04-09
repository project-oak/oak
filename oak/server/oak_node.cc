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

#include "oak/server/oak_node.h"

#include <openssl/sha.h>

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "src/binary-reader.h"
#include "src/error-formatter.h"
#include "src/error.h"
#include "src/interp/binary-reader-interp.h"
#include "src/interp/interp.h"

namespace oak {

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

static ::absl::Span<const char> ReadMemory(::wabt::interp::Environment* env, const uint32_t offset,
                                           const uint32_t size) {
  return absl::MakeConstSpan(env->GetMemory(0)->data).subspan(offset, size);
}

static const std::string ReadString(wabt::interp::Environment* env, const uint32_t offset,
                                    const uint32_t size) {
  ::absl::Span<const char> memory = ReadMemory(env, offset, size);
  return std::string(memory.cbegin(), memory.cend());
}

template <class Iterator>
static void WriteMemory(wabt::interp::Environment* env, const uint32_t offset, Iterator begin,
                        Iterator end) {
  std::copy(begin, end, env->GetMemory(0)->data.begin() + offset);
}

static void WriteMemory(wabt::interp::Environment* env, const uint32_t offset,
                        const absl::Span<const char> data) {
  WriteMemory(env, offset, data.cbegin(), data.cend());
}

static void WriteString(wabt::interp::Environment* env, const uint32_t offset,
                        const std::string str) {
  WriteMemory(env, offset, str.cbegin(), str.cend());
}

// Native implementation of the `oak.print` host function.
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

// Native implementation of the `oak.get_time` host function.
static wabt::interp::HostFunc::Callback OakGetTime(wabt::interp::Environment* env) {
  return [env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
               const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    auto now = std::chrono::system_clock::now();
    auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
    results[0].set_i64(ns);
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

std::string Sha256Hash(const std::string& data) {
  SHA256_CTX context;
  SHA256_Init(&context);
  SHA256_Update(&context, data.data(), data.size());
  std::vector<uint8_t> hash(SHA256_DIGEST_LENGTH);
  SHA256_Final(hash.data(), &context);
  return std::string(hash.cbegin(), hash.cend());
}

OakNode::OakNode(const std::string& node_id, const std::string& module)
    : Service(), node_id_(node_id), module_hash_sha_256_(Sha256Hash(module)) {
  LOG(INFO) << "Creating Oak Node";
  wabt::Result result;
  InitEnvironment(&env_);
  LOG(INFO) << "Func count: " << env_.GetFuncCount();

  // TODO: Check that all the expected exports are present in the module.

  wabt::Errors errors;

  LOG(INFO) << "Reading module";
  result = ReadModule(module, &env_, &errors, &module_);
  if (wabt::Succeeded(result)) {
    LOG(INFO) << "Read module";
    wabt::interp::Thread::Options thread_options;

    // wabt::Stream* trace_stream = s_stdout_stream.get();
    wabt::Stream* trace_stream = nullptr;
    wabt::interp::Executor executor(&env_, trace_stream, thread_options);
    LOG(INFO) << "Executing module";

    wabt::interp::TypedValues args;

    wabt::interp::ExecResult exec_result =
        executor.RunExportByName(module_, "oak_initialize", args);

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
}

// Register all available host functions so that they are available to the Oak Module at runtime.
//
// TODO: Selectively install only the host functions allowed by the policies associated with the Oak
// Module.
void OakNode::InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");

  oak_module->AppendFuncExport(
      "print",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{}),
      PrintString(env));
  oak_module->AppendFuncExport(
      "get_time",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{},
                                  std::vector<wabt::Type>{wabt::Type::I64}),
      OakGetTime(env));

  oak_module->AppendFuncExport(
      "read_method_name",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakReadMethodName(env));
  oak_module->AppendFuncExport(
      "read",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakRead(env));
  oak_module->AppendFuncExport(
      "write",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakWrite(env));
}

::wabt::interp::HostFunc::Callback OakNode::OakReadMethodName(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    for (auto const& arg : args) {
      LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
    }

    uint32_t p = args[0].get_i32();
    uint32_t len = args[1].get_i32();

    std::string grpc_method_name = server_context_->method();

    uint32_t end = len;
    if (end > grpc_method_name.size()) {
      end = grpc_method_name.size();
    }

    WriteString(env, p, grpc_method_name);
    results[0].set_i32(end);

    return wabt::interp::Result::Ok;
  };
}

::wabt::interp::HostFunc::Callback OakNode::OakRead(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    for (auto const& arg : args) {
      LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
    }
    uint32_t offset = args[0].get_i32();
    uint32_t size = args[1].get_i32();

    if (size > module_data_input_.size()) {
      size = module_data_input_.size();
    }
    WriteMemory(env, offset, module_data_input_.cbegin(), module_data_input_.cbegin() + size);
    results[0].set_i32(size);
    module_data_input_.remove_prefix(size);

    return ::wabt::interp::Result::Ok;
  };
}

::wabt::interp::HostFunc::Callback OakNode::OakWrite(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
    for (auto const& arg : args) {
      LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
    }
    uint32_t offset = args[0].get_i32();
    uint32_t size = args[1].get_i32();

    ::absl::Span<const char> memory = ReadMemory(env, offset, size);
    module_data_output_->insert(module_data_output_->end(), memory.cbegin(), memory.cend());
    results[0].set_i32(size);

    return wabt::interp::Result::Ok;
  };
}

::grpc::Status OakNode::ProcessModuleInvocation(::grpc::GenericServerContext* context,
                                                const std::vector<uint8_t>& request_data,
                                                std::vector<uint8_t>* response_data) {
  LOG(INFO) << "Handling gRPC call: " << context->method();
  server_context_ = context;

  ::absl::MutexLock lock(&module_data_mutex_);
  module_data_input_ = ::absl::Span<const uint8_t>(request_data);
  module_data_output_ = response_data;

  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Thread::Options thread_options;
  wabt::interp::Executor executor(&env_, trace_stream, thread_options);

  // Note that inputs and outputs are not bound to the args of the invocation, because the memory of
  // the receiving buffer must be allocated and managed by the runtime rather than the interpreter.
  // The Oak Module can consume the input data by calling the `oak.read` host function, and produce
  // output data by calling the `oak.write` host function.
  wabt::interp::TypedValues args;
  wabt::interp::ExecResult exec_result =
      executor.RunExportByName(module_, "oak_handle_grpc_call", args);

  if (exec_result.result != wabt::interp::Result::Ok) {
    // TODO: This should be an error?
    LOG(WARNING) << "Could not handle gRPC call: "
                 << wabt::interp::ResultToString(exec_result.result);
  }
  return ::grpc::Status::OK;
}

::grpc::Status OakNode::GetAttestation(::grpc::ServerContext* context,
                                       const ::oak::GetAttestationRequest* request,
                                       ::oak::GetAttestationResponse* response) {
  response->set_module_hash_sha_256(module_hash_sha_256_);
  return ::grpc::Status::OK;
}

}  // namespace oak

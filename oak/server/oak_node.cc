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

#include <iostream>
#include <utility>

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "oak/server/buffer_channel.h"
#include "oak/server/logging_channel.h"
#include "oak/server/wabt_output.h"
#include "src/binary-reader.h"
#include "src/error-formatter.h"
#include "src/error.h"
#include "src/interp/binary-reader-interp.h"

namespace oak {

// From https://github.com/WebAssembly/wabt/blob/master/src/tools/wasm-interp.cc .

static std::unique_ptr<wabt::FileStream> s_log_stream = wabt::FileStream::CreateStdout();
static std::unique_ptr<wabt::FileStream> s_stdout_stream = wabt::FileStream::CreateStdout();

static absl::Span<const char> ReadMemory(wabt::interp::Environment* env, const uint32_t offset,
                                         const uint32_t size) {
  return absl::MakeConstSpan(env->GetMemory(0)->data).subspan(offset, size);
}

static const std::string ReadString(wabt::interp::Environment* env, const uint32_t offset,
                                    const uint32_t size) {
  absl::Span<const char> memory = ReadMemory(env, offset, size);
  return std::string(memory.cbegin(), memory.cend());
}

static void WriteMemory(wabt::interp::Environment* env, const uint32_t offset,
                        const absl::Span<const char> data) {
  std::copy(data.cbegin(), data.cend(), env->GetMemory(0)->data.begin() + offset);
}

// Creates a TypedValue of type i64 with the specified inner value.
static wabt::interp::TypedValue MakeI64(uint64_t v) {
  wabt::interp::TypedValue tv(wabt::Type::I64);
  tv.set_i64(v);
  return tv;
}

static void LogHostFunctionCall(const wabt::interp::HostFunc* func,
                                const wabt::interp::TypedValues& args) {
  LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name;
  for (auto const& arg : args) {
    LOG(INFO) << "Arg: " << wabt::interp::TypedValueToString(arg);
  }
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

// Describes an expected export from an Oak module.
struct RequiredExport {
  std::string name_;
  bool mandatory_;
  wabt::interp::FuncSignature sig_;
};

}  // namespace oak

std::ostream& operator<<(std::ostream& os, const oak::RequiredExport& r) {
  return os << (r.mandatory_ ? "required" : "optional") << " export '" << r.name_
            << "' with signature " << &r.sig_;
}

namespace oak {

const RequiredExport kRequiredExports[] = {
    {"oak_initialize", true, {}},
    {"oak_handle_grpc_call", true, {}},
    {"oak_finalize", false, {}},
};

// Check module exports all required functions with the correct signatures,
// returning true if so.
static bool CheckModuleExport(wabt::interp::Environment* env, wabt::interp::DefinedModule* module,
                              const RequiredExport& req) {
  LOG(INFO) << "check for " << req;
  wabt::interp::Export* exp = module->GetExport(req.name_);
  if (exp == nullptr) {
    if (req.mandatory_) {
      LOG(WARNING) << "Could not find required export '" << req.name_ << "' in module";
      return false;
    }
    LOG(INFO) << "optional import '" << req.name_ << "' missing";
    return true;
  }
  if (exp->kind != wabt::ExternalKind::Func) {
    LOG(WARNING) << "Required export of kind " << exp->kind << " not func in module";
    return false;
  }
  LOG(INFO) << "check signature of function #" << exp->index;
  wabt::interp::Func* func = env->GetFunc(exp->index);
  if (func == nullptr) {
    LOG(WARNING) << "failed to retrieve function #" << exp->index;
    return false;
  }
  if (func->sig_index >= env->GetFuncSignatureCount()) {
    LOG(WARNING) << "Function #" << func->sig_index << " beyond range of signature types";
    return false;
  }
  wabt::interp::FuncSignature* sig = env->GetFuncSignature(func->sig_index);
  if (sig == nullptr) {
    LOG(WARNING) << "Could not find signature for function #" << exp->index;
    return false;
  }
  LOG(INFO) << "function #" << exp->index << " has type #" << func->sig_index << " with signature "
            << *sig;
  if ((sig->param_types != req.sig_.param_types) || (sig->result_types != req.sig_.result_types)) {
    LOG(WARNING) << "Function signature mismatch for " << req.name_ << ": got " << *sig << ", want "
                 << req.sig_;
    return false;
  }
  return true;
}
static bool CheckModuleExports(wabt::interp::Environment* env,
                               wabt::interp::DefinedModule* module) {
  bool rc = true;
  for (const RequiredExport& req : kRequiredExports) {
    if (!CheckModuleExport(env, module, req)) {
      rc = false;
    }
  }
  return rc;
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

  wabt::Errors errors;
  LOG(INFO) << "Reading module";
  result = ReadModule(module, &env_, &errors, &module_);
  if (wabt::Succeeded(result)) {
    LOG(INFO) << "Read module";
    if (!CheckModuleExports(&env_, module_)) {
      LOG(WARNING) << "Failed to validate module";
    }

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
void OakNode::InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");
  oak_module->AppendFuncExport(
      "channel_read",
      wabt::interp::FuncSignature(
          std::vector<wabt::Type>{wabt::Type::I64, wabt::Type::I32, wabt::Type::I32},
          std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelRead(env));
  oak_module->AppendFuncExport(
      "channel_write",
      wabt::interp::FuncSignature(
          std::vector<wabt::Type>{wabt::Type::I64, wabt::Type::I32, wabt::Type::I32},
          std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelWrite(env));
}

wabt::interp::HostFunc::Callback OakNode::OakChannelRead(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    Handle channel_handle = args[0].get_i64();
    uint32_t offset = args[1].get_i32();
    uint32_t size = args[2].get_i32();

    if (channels_.count(channel_handle) == 0) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
    }
    std::unique_ptr<Channel>& channel = channels_.at(channel_handle);

    absl::Span<const char> data = channel->Read(size);
    WriteMemory(env, offset, data);
    results[0].set_i32(data.size());

    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback OakNode::OakChannelWrite(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    Handle channel_handle = args[0].get_i64();
    uint32_t offset = args[1].get_i32();
    uint32_t size = args[2].get_i32();

    if (channels_.count(channel_handle) == 0) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
    }
    std::unique_ptr<Channel>& channel = channels_.at(channel_handle);

    absl::Span<const char> data = ReadMemory(env, offset, size);
    channel->Write(data);
    results[0].set_i32(data.size());

    return wabt::interp::Result::Ok;
  };
}

grpc::Status OakNode::ProcessModuleInvocation(grpc::GenericServerContext* context,
                                              const std::vector<char>& request_data,
                                              std::vector<char>* response_data) {
  LOG(INFO) << "Handling gRPC call: " << context->method();
  server_context_ = context;

  // Store a copy of the gRPC method name so that we can refer to it via a Span when the Module
  // tries to read it from a channel; otherwise we would need to allocate a new string every time
  // and ensure it can outlive the Span reference.
  grpc_method_name_ = context->method();

  // Create the gRPC channel, used by the module to perform basic input and output.
  std::unique_ptr<Channel> grpc_channel =
      absl::make_unique<BufferChannel>(request_data, response_data);
  channels_[GRPC_CHANNEL_HANDLE] = std::move(grpc_channel);
  LOG(INFO) << "Created gRPC channel";

  // Create the gRPC method name channel, used by the module to read the gRPC method name from the
  // current context.
  std::unique_ptr<Channel> grpc_method_name_channel =
      absl::make_unique<BufferChannel>(grpc_method_name_, nullptr);
  channels_[GRPC_METHOD_NAME_CHANNEL_HANDLE] = std::move(grpc_method_name_channel);
  LOG(INFO) << "Created gRPC method name channel";

  // Create the logging channel, used by the module to log statements for debugging.
  std::unique_ptr<Channel> logging_channel = absl::make_unique<LoggingChannel>();
  channels_[LOGGING_CHANNEL_HANDLE] = std::move(logging_channel);
  LOG(INFO) << "Created logging channel";

  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Thread::Options thread_options;
  wabt::interp::Executor executor(&env_, trace_stream, thread_options);

  wabt::interp::TypedValues args = {};
  wabt::interp::ExecResult exec_result =
      executor.RunExportByName(module_, "oak_handle_grpc_call", args);

  if (exec_result.result != wabt::interp::Result::Ok) {
    // TODO: This should be an error?
    LOG(WARNING) << "Could not handle gRPC call: "
                 << wabt::interp::ResultToString(exec_result.result);
  }

  // Drop all the channels used in the current invocation.
  channels_ = std::unordered_map<Handle, std::unique_ptr<Channel>>();

  return grpc::Status::OK;
}

grpc::Status OakNode::GetAttestation(grpc::ServerContext* context,
                                     const GetAttestationRequest* request,
                                     GetAttestationResponse* response) {
  response->set_module_hash_sha_256(module_hash_sha_256_);
  return ::grpc::Status::OK;
}

}  // namespace oak

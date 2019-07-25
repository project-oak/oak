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
#include "oak/server/logging_channel.h"
#include "oak/server/status.h"
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

static void WriteMemory(wabt::interp::Environment* env, const uint32_t offset,
                        const absl::Span<const char> data) {
  std::copy(data.cbegin(), data.cend(), env->GetMemory(0)->data.begin() + offset);
}

static void WriteI32(wabt::interp::Environment* env, const uint32_t offset, const int32_t value) {
  uint32_t v = static_cast<uint32_t>(value);
  auto base = env->GetMemory(0)->data.begin() + offset;
  base[0] = v & 0xff;
  base[1] = (v >> 8) & 0xff;
  base[2] = (v >> 16) & 0xff;
  base[3] = (v >> 24) & 0xff;
}

static void LogHostFunctionCall(const wabt::interp::HostFunc* func,
                                const wabt::interp::TypedValues& args) {
  std::stringstream params;
  bool first = true;
  for (auto const& arg : args) {
    params << std::string(first ? "" : ", ") << wabt::interp::TypedValueToString(arg);
    first = false;
  }
  LOG(INFO) << "Called host function: " << func->module_name << "." << func->field_name << "("
            << params.str() << ")";
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

  return wabt::ReadBinaryInterp(env, module_bytes.data(), module_bytes.size(), options, errors,
                                out_module);
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

OakNode::OakNode() : Service() {}

std::unique_ptr<OakNode> OakNode::Create(const std::string& module) {
  LOG(INFO) << "Creating Oak Node";

  std::unique_ptr<OakNode> node = absl::WrapUnique(new OakNode());
  node->InitEnvironment(&node->env_);
  LOG(INFO) << "Host func count: " << node->env_.GetFuncCount();

  wabt::Errors errors;
  LOG(INFO) << "Reading module";
  wabt::Result result = ReadModule(module, &node->env_, &errors, &node->module_);
  if (!wabt::Succeeded(result)) {
    LOG(WARNING) << "Could not read module: " << result;
    LOG(WARNING) << "Errors: " << wabt::FormatErrorsToString(errors, wabt::Location::Type::Binary);
    return nullptr;
  }

  LOG(INFO) << "Reading module done";
  if (!CheckModuleExports(&node->env_, node->module_)) {
    LOG(WARNING) << "Failed to validate module";
    return nullptr;
  }

  wabt::interp::Thread::Options thread_options;
  // wabt::Stream* trace_stream = s_stdout_stream.get();
  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Executor executor(&node->env_, trace_stream, thread_options);
  LOG(INFO) << "Executing module";

  // Create a (persistent) logging channel to allow the module to log during initialization.
  node->channel_halves_[LOGGING_CHANNEL_HANDLE] = absl::make_unique<LoggingChannelHalf>();
  LOG(INFO) << "Created logging channel " << LOGGING_CHANNEL_HANDLE;

  wabt::interp::TypedValues args;
  wabt::interp::ExecResult exec_result =
      executor.RunExportByName(node->module_, "oak_initialize", args);

  if (exec_result.result != wabt::interp::Result::Ok) {
    LOG(WARNING) << "Could not execute module initialization";
    wabt::interp::WriteResult(s_stdout_stream.get(), "error", exec_result.result);
    // TODO: Print error.
    return nullptr;
  }
  LOG(INFO) << "Executed module initialization";

  // Now that initialization has completed, create the channels needed for gRPC interactions.
  {
    // Method name channel: keep the write half in C++, but map the read half to a
    // well-known channel handle.
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[GRPC_METHOD_NAME_CHANNEL_HANDLE] =
        absl::make_unique<MessageChannelReadHalf>(channel);
    node->name_half_ = absl::make_unique<MessageChannelWriteHalf>(channel);
    LOG(INFO) << "Created gRPC method name channel: " << GRPC_METHOD_NAME_CHANNEL_HANDLE;
  }
  {
    // Incoming request channel: keep the write half in C++, but map the read
    // half to a well-known channel handle.
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[GRPC_IN_CHANNEL_HANDLE] =
        absl::make_unique<MessageChannelReadHalf>(channel);
    node->req_half_ = absl::make_unique<MessageChannelWriteHalf>(channel);
    LOG(INFO) << "Created gRPC input channel: " << GRPC_IN_CHANNEL_HANDLE;
  }
  {
    // Outgoing response channel: keep the read half in C++, but map the write
    // half to a well-known channel handle.
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[GRPC_OUT_CHANNEL_HANDLE] =
        absl::make_unique<MessageChannelWriteHalf>(channel);
    node->rsp_half_ = absl::make_unique<MessageChannelReadHalf>(channel);
    LOG(INFO) << "Created gRPC output channel: " << GRPC_IN_CHANNEL_HANDLE;
  }

  return node;
}

// Register all available host functions so that they are available to the Oak Module at runtime.
void OakNode::InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");
  oak_module->AppendFuncExport(
      "channel_read",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I64, wabt::Type::I32,
                                                          wabt::Type::I32, wabt::Type::I32},
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
    uint32_t size_offset = args[3].get_i32();

    if (channel_halves_.count(channel_handle) == 0) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
      results[0].set_i32(STATUS_ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }
    std::unique_ptr<ChannelHalf>& channel = channel_halves_.at(channel_handle);

    ReadResult result = channel->Read(size);
    if (result.required_size > 0) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: buffer too small: " << size << " < "
                << result.required_size;
      WriteI32(env, size_offset, result.required_size);
      results[0].set_i32(STATUS_ERR_BUFFER_TOO_SMALL);
    } else if (result.data == nullptr) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: no message available";
      WriteI32(env, size_offset, 0);
      results[0].set_i32(STATUS_OK);
    } else {
      LOG(INFO) << "channel_read[" << channel_handle << "]: read message of size "
                << result.data->size();
      WriteI32(env, size_offset, result.data->size());
      WriteMemory(env, offset, absl::Span<char>(result.data->data(), result.data->size()));
      results[0].set_i32(STATUS_OK);
    }

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

    if (channel_halves_.count(channel_handle) == 0) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
      results[0].set_i32(STATUS_ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }
    std::unique_ptr<ChannelHalf>& channel = channel_halves_.at(channel_handle);

    // Copy the data from the Wasm linear memory.
    absl::Span<const char> origin = ReadMemory(env, offset, size);
    std::unique_ptr<Message> data = absl::make_unique<Message>(origin.begin(), origin.end());
    LOG(INFO) << "channel_write[" << channel_handle << "]: write message of size " << data->size();
    channel->Write(std::move(data));
    results[0].set_i32(STATUS_OK);

    return wabt::interp::Result::Ok;
  };
}

OakNode::InvocationResult OakNode::ProcessModuleInvocation(grpc::GenericServerContext* context,
                                                           std::unique_ptr<Message> request_data) {
  LOG(INFO) << "Handling gRPC call: " << context->method();

  // Write the method name to the name channel.
  const std::string& method_name = context->method();
  std::unique_ptr<Message> method_data =
      absl::make_unique<Message>(method_name.begin(), method_name.end());
  name_half_->Write(std::move(method_data));
  LOG(INFO) << "Wrote method name of size " << method_name.size() << " to name channel";

  // Write the incoming request to the input channel.
  size_t req_size = request_data->size();
  req_half_->Write(std::move(request_data));
  LOG(INFO) << "Wrote request of size " << req_size << " to input channel";

  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Thread::Options thread_options;
  wabt::interp::Executor executor(&env_, trace_stream, thread_options);

  wabt::interp::TypedValues args = {};
  wabt::interp::ExecResult exec_result =
      executor.RunExportByName(module_, "oak_handle_grpc_call", args);

  InvocationResult result;
  if (exec_result.result != wabt::interp::Result::Ok) {
    std::string err = wabt::interp::ResultToString(exec_result.result);
    LOG(ERROR) << "Could not handle gRPC call: " << err;
    result.status = grpc::Status(grpc::StatusCode::INTERNAL, err);
    return result;
  }
  ReadResult rsp_result = rsp_half_->Read(INT_MAX);
  if (rsp_result.required_size > 0) {
    LOG(ERROR) << "Message size too large: " << rsp_result.required_size;
    result.status = grpc::Status(grpc::StatusCode::INTERNAL, "Message size too large");
    return result;
  }
  if (rsp_result.data != nullptr) {
    LOG(INFO) << "Read message of size " << rsp_result.data->size() << " from output channel";
  } else {
    LOG(INFO) << "No response on output channel";
  }
  result.status = grpc::Status::OK;
  result.data = std::move(rsp_result.data);
  return result;
}

grpc::Status OakNode::GetAttestation(grpc::ServerContext* context,
                                     const GetAttestationRequest* request,
                                     GetAttestationResponse* response) {
  // TODO: Move this method to the application and implement it there.
  return ::grpc::Status::OK;
}

}  // namespace oak

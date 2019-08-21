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
#include "oak/proto/oak_api.pb.h"
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

static uint64_t ReadU64(wabt::interp::Environment* env, const uint32_t offset) {
  auto base = env->GetMemory(0)->data.begin() + offset;
  return (static_cast<uint64_t>(base[0]) | (static_cast<uint64_t>(base[1]) << 8) |
          (static_cast<uint64_t>(base[2]) << 16) | (static_cast<uint64_t>(base[3]) << 24) |
          (static_cast<uint64_t>(base[4]) << 32) | (static_cast<uint64_t>(base[5]) << 40) |
          (static_cast<uint64_t>(base[6]) << 48) | (static_cast<uint64_t>(base[7]) << 56));
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
    {
        "oak_main",
        true,
        wabt::interp::FuncSignature(std::vector<wabt::Type>{},
                                    std::vector<wabt::Type>{wabt::Type::I32}),
    },
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

static void RunModule(wabt::interp::Environment* env, wabt::interp::DefinedModule* module) {
  wabt::interp::Thread::Options thread_options;
  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Executor executor(env, trace_stream, thread_options);

  LOG(INFO) << "module execution thread: run oak_main";
  wabt::interp::TypedValues args;
  wabt::interp::ExecResult exec_result = executor.RunExportByName(module, "oak_main", args);

  if (exec_result.result != wabt::interp::Result::Ok) {
    LOG(ERROR) << "execution failure: " << wabt::interp::ResultToString(exec_result.result);
  }
  uint32_t status = exec_result.values[0].get_i32();
  LOG(WARNING) << "module execution terminated with status " << status;
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

  // Create a logging channel for the module.
  {
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[ChannelHandle::LOGGING] =
        absl::make_unique<MessageChannelWriteHalf>(channel);
    LOG(INFO) << "Created logging channel " << ChannelHandle::LOGGING;

    // Spawn a thread that reads and logs messages on this channel forever.
    std::thread t([channel] {
      std::unique_ptr<MessageChannelReadHalf> read_chan =
          absl::make_unique<MessageChannelReadHalf>(channel);
      while (true) {
        ReadResult result = read_chan->BlockingRead(INT_MAX);
        if (result.required_size > 0) {
          LOG(ERROR) << "Message size too large: " << result.required_size;
          return;
        }
        LOG(INFO) << "LOG: " << std::string(result.data->data(), result.data->size());
      }
    });
    // TODO: join() instead when we have node termination
    t.detach();
  }

  // Create the channels needed for gRPC interactions.
  {
    // Incoming request channel: keep the write half in C++, but map the read
    // half to a well-known channel handle.
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[ChannelHandle::GRPC_IN] =
        absl::make_unique<MessageChannelReadHalf>(channel);
    node->req_half_ = absl::make_unique<MessageChannelWriteHalf>(channel);
    LOG(INFO) << "Created gRPC input channel: " << ChannelHandle::GRPC_IN;
  }
  {
    // Outgoing response channel: keep the read half in C++, but map the write
    // half to a well-known channel handle.
    std::shared_ptr<MessageChannel> channel = std::make_shared<MessageChannel>();
    node->channel_halves_[ChannelHandle::GRPC_OUT] =
        absl::make_unique<MessageChannelWriteHalf>(channel);
    node->rsp_half_ = absl::make_unique<MessageChannelReadHalf>(channel);
    LOG(INFO) << "Created gRPC output channel: " << ChannelHandle::GRPC_IN;
  }

  // Spin up a per-node Wasm thread to run forever; the Node object must
  // outlast this thread.
  LOG(INFO) << "Executing module oak_main";
  std::thread t([&node] { RunModule(&node->env_, node->module_); });
  // TODO: join() instead when we have node termination
  t.detach();
  LOG(INFO) << "Started module execution thread";

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

  oak_module->AppendFuncExport(
      "wait_on_channels",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakWaitOnChannels(env));
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
      results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }
    std::unique_ptr<ChannelHalf>& channel = channel_halves_.at(channel_handle);

    ReadResult result = channel->Read(size);
    if (result.required_size > 0) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: buffer too small: " << size << " < "
                << result.required_size;
      WriteI32(env, size_offset, result.required_size);
      results[0].set_i32(OakStatus::ERR_BUFFER_TOO_SMALL);
    } else if (result.data == nullptr) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: no message available";
      WriteI32(env, size_offset, 0);
      results[0].set_i32(OakStatus::OK);
    } else {
      LOG(INFO) << "channel_read[" << channel_handle << "]: read message of size "
                << result.data->size();
      WriteI32(env, size_offset, result.data->size());
      WriteMemory(env, offset, absl::Span<char>(result.data->data(), result.data->size()));
      results[0].set_i32(OakStatus::OK);
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
      results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }
    std::unique_ptr<ChannelHalf>& channel = channel_halves_.at(channel_handle);

    // Copy the data from the Wasm linear memory.
    absl::Span<const char> origin = ReadMemory(env, offset, size);
    std::unique_ptr<Message> data = absl::make_unique<Message>(origin.begin(), origin.end());
    LOG(INFO) << "channel_write[" << channel_handle << "]: write message of size " << data->size();
    channel->Write(std::move(data));
    results[0].set_i32(OakStatus::OK);

    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback OakNode::OakWaitOnChannels(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    uint32_t offset = args[0].get_i32();
    uint32_t count = args[1].get_i32();
    results[0].set_i32(OakStatus::OK);

    if (count == 0) {
      LOG(INFO) << "Waiting on no channels";
      return wabt::interp::Result::Ok;
    }

    uint64_t handle0 = ReadU64(env, offset);
    // TODO: Drop hardcoded single channel
    if (handle0 != ChannelHandle::GRPC_IN) {
      LOG(ERROR) << "Read of unexpected handle " << handle0;
      return wabt::interp::Result::Ok;
    }

    req_half_->Await();
    // TODO: Mark just the relevant channels as ready to read.
    auto base = env->GetMemory(0)->data.begin() + offset;
    base[8] = 0x01;
    return wabt::interp::Result::Ok;
  };
}

void OakNode::ProcessModuleInvocation(grpc::GenericServerContext* context,
                                      std::unique_ptr<Message> request_data) {
  LOG(INFO) << "Handling gRPC call: " << context->method();

  // Build an encapsulation of the gRPC request invocation and write its serialized
  // form to the gRPC input channel.
  oak::GrpcRequest grpc_in;
  grpc_in.set_method_name(context->method());
  google::protobuf::Any* any = new google::protobuf::Any();
  any->set_value(request_data->data(), request_data->size());
  grpc_in.set_allocated_req_msg(any);
  grpc_in.set_last(true);
  std::string encap_req;
  grpc_in.SerializeToString(&encap_req);
  // TODO: figure out a way to avoid the extra copy (into then out of std::string)
  std::unique_ptr<Message> encap_data =
      absl::make_unique<Message>(encap_req.begin(), encap_req.end());
  req_half_->Write(std::move(encap_data));
  LOG(INFO) << "Wrote encapsulated request to input channel";
}

oak::GrpcResponse OakNode::NextResponse() {
  oak::GrpcResponse grpc_out;
  ReadResult rsp_result;
  // Block until we can read a single queued GrpcResponse message (in serialized form) from the
  // response channel.
  rsp_result = rsp_half_->BlockingRead(INT_MAX);
  if (rsp_result.required_size > 0) {
    LOG(ERROR) << "Message size too large: " << rsp_result.required_size;
    google::rpc::Status* status = new google::rpc::Status();
    status->set_code(grpc::StatusCode::INTERNAL);
    status->set_message("Message size too large");
    grpc_out.set_allocated_status(status);
    return grpc_out;
  }

  LOG(INFO) << "Read encapsulated message of size " << rsp_result.data->size()
            << " from output channel";
  grpc_out.ParseFromString(std::string(rsp_result.data->data(), rsp_result.data->size()));
  return grpc_out;
}

grpc::Status OakNode::GetAttestation(grpc::ServerContext* context,
                                     const GetAttestationRequest* request,
                                     GetAttestationResponse* response) {
  // TODO: Move this method to the application and implement it there.
  return ::grpc::Status::OK;
}

}  // namespace oak

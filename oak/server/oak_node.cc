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
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
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

static wabt::Result ReadModule(const std::string& module_bytes, wabt::interp::Environment* env,
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

const std::vector<RequiredExport> kRequiredExports({
    {
        "oak_main",
        true,
        wabt::interp::FuncSignature(std::vector<wabt::Type>{},
                                    std::vector<wabt::Type>{wabt::Type::I32}),
    },
});

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
  return std::all_of(
      kRequiredExports.begin(), kRequiredExports.end(),
      [env, module](const RequiredExport& req) { return CheckModuleExport(env, module, req); });
}

OakNode::OakNode(const std::string& name) : NodeThread(name), next_handle_(0) {}

std::unique_ptr<OakNode> OakNode::Create(const std::string& name, const std::string& module) {
  LOG(INFO) << "Creating Oak Node";

  std::unique_ptr<OakNode> node = absl::WrapUnique(new OakNode(name));
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

  return node;
}

Handle OakNode::AddNamedChannel(const std::string& port_name,
                                std::unique_ptr<ChannelHalf> channel_half) {
  Handle handle = ++next_handle_;
  LOG(INFO) << "port name '" << port_name << "' maps to handle " << handle;
  named_channels_[port_name] = handle;
  channel_halves_[handle] = std::move(channel_half);
  return handle;
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
  oak_module->AppendFuncExport(
      "channel_find",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I64}),
      this->OakChannelFind(env));
}

void OakNode::Run() {
  wabt::interp::Thread::Options thread_options;
  wabt::Stream* trace_stream = nullptr;
  wabt::interp::Executor executor(&env_, trace_stream, thread_options);

  LOG(INFO) << "module execution thread: run oak_main";
  wabt::interp::TypedValues args;
  wabt::interp::ExecResult exec_result = executor.RunExportByName(module_, "oak_main", args);

  if (exec_result.result != wabt::interp::Result::Ok) {
    LOG(ERROR) << "execution failure: " << wabt::interp::ResultToString(exec_result.result);
    return;
  }
  uint32_t status = exec_result.values[0].get_i32();
  LOG(WARNING) << "module execution terminated with status " << status;
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
    auto data = absl::make_unique<Message>(origin.begin(), origin.end());
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
      LOG(INFO) << "Waiting on no channels, return immediately";
      return wabt::interp::Result::Ok;
    }

    std::vector<uint64_t> handles;
    handles.reserve(count);
    for (uint32_t ii = 0; ii < count; ii++) {
      uint64_t handle = ReadU64(env, offset + (9 * ii));
      handles.push_back(handle);
    }
    bool done = false;
    while (!done) {
      for (uint32_t ii = 0; ii < count; ii++) {
        uint64_t handle = handles[ii];
        ChannelHalfTable::iterator it = channel_halves_.find(handle);
        if (it == channel_halves_.end()) {
          LOG(WARNING) << "Waiting on non-existent channel handle " << handle;
          continue;
        }
        ChannelHalf* channel = it->second.get();
        if (channel->CanRead()) {
          LOG(INFO) << "Message available on handle " << handle;
          done = true;
          auto base = env->GetMemory(0)->data.begin() + offset + (9 * ii);
          base[8] = 0x01;
        }
      }
      if (termination_pending_.load()) {
        LOG(WARNING) << "Node is pending termination";
        results[0].set_i32(OakStatus::ERR_CHANNEL_CLOSED);
        done = true;
      } else if (!done) {
        // TODO: get rid of polling wait
        absl::SleepFor(absl::Milliseconds(100));
      }
    }
    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback OakNode::OakChannelFind(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    uint32_t offset = args[0].get_i32();
    uint32_t length = args[1].get_i32();
    results[0].set_i64(0);

    auto base = env->GetMemory(0)->data.begin() + offset;
    std::string port_name(base, base + length);

    auto it = named_channels_.find(port_name);
    if (it != named_channels_.end()) {
      results[0].set_i64(it->second);
    }

    return wabt::interp::Result::Ok;
  };
}

}  // namespace oak

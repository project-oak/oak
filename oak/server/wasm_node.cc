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

#include "oak/server/wasm_node.h"

#include <iostream>
#include <utility>

#include "absl/memory/memory.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "asylo/util/logging.h"
#include "oak/proto/oak_api.pb.h"
#include "oak/server/channel.h"
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

static void WriteU64(wabt::interp::Environment* env, const uint32_t offset, const uint64_t v) {
  auto base = env->GetMemory(0)->data.begin() + offset;
  base[0] = v & 0xff;
  base[1] = (v >> 8) & 0xff;
  base[2] = (v >> 16) & 0xff;
  base[3] = (v >> 24) & 0xff;
  base[4] = (v >> 32) & 0xff;
  base[5] = (v >> 40) & 0xff;
  base[6] = (v >> 48) & 0xff;
  base[7] = (v >> 56) & 0xff;
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
            << "' with signature " << r.sig_;
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

WasmNode::WasmNode(const std::string& name) : NodeThread(name) {}

std::unique_ptr<WasmNode> WasmNode::Create(const std::string& name, const std::string& module) {
  LOG(INFO) << "Creating Wasm Node";

  std::unique_ptr<WasmNode> node = absl::WrapUnique(new WasmNode(name));
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

// Register all available host functions so that they are available to the Oak Module at runtime.
void WasmNode::InitEnvironment(wabt::interp::Environment* env) {
  wabt::interp::HostModule* oak_module = env->AppendHostModule("oak");
  oak_module->AppendFuncExport(
      "channel_read",
      wabt::interp::FuncSignature(
          std::vector<wabt::Type>{wabt::Type::I64, wabt::Type::I32, wabt::Type::I32,
                                  wabt::Type::I32, wabt::Type::I32, wabt::Type::I32,
                                  wabt::Type::I32},
          std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelRead(env));
  oak_module->AppendFuncExport(
      "channel_write",
      wabt::interp::FuncSignature(
          std::vector<wabt::Type>{wabt::Type::I64, wabt::Type::I32, wabt::Type::I32,
                                  wabt::Type::I32, wabt::Type::I32},
          std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelWrite(env));

  oak_module->AppendFuncExport(
      "wait_on_channels",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakWaitOnChannels(env));
  oak_module->AppendFuncExport(
      "channel_create",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelCreate(env));
  oak_module->AppendFuncExport(
      "channel_close",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I64},
                                  std::vector<wabt::Type>{wabt::Type::I32}),
      this->OakChannelClose(env));
  oak_module->AppendFuncExport(
      "channel_find",
      wabt::interp::FuncSignature(std::vector<wabt::Type>{wabt::Type::I32, wabt::Type::I32},
                                  std::vector<wabt::Type>{wabt::Type::I64}),
      this->OakChannelFind(env));
}

void WasmNode::Run() {
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

wabt::interp::HostFunc::Callback WasmNode::OakChannelRead(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    Handle channel_handle = args[0].get_i64();
    uint32_t offset = args[1].get_i32();
    uint32_t size = args[2].get_i32();
    uint32_t size_offset = args[3].get_i32();
    uint32_t handle_space_offset = args[4].get_i32();
    uint32_t handle_space_count = args[5].get_i32();
    uint32_t handle_count_offset = args[6].get_i32();

    // Borrowing a reference to the channel is safe because the node is single
    // threaded and so cannot invoke channel_close while channel_read is
    // ongoing.
    MessageChannelReadHalf* channel = BorrowReadChannel(channel_handle);
    if (channel == nullptr) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
      results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }

    ReadResult result = channel->Read(size, handle_space_count);
    if (result.required_size > 0) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: buffer too small: " << size << " < "
                << result.required_size;
      WriteI32(env, size_offset, result.required_size);
      WriteI32(env, handle_count_offset, result.required_channels);
      results[0].set_i32(OakStatus::ERR_BUFFER_TOO_SMALL);
      return wabt::interp::Result::Ok;
    } else if (result.required_channels > 0) {
      LOG(INFO) << "channel_read[" << channel_handle
                << "]: handle space too small: " << handle_space_count << " < "
                << result.required_channels;
      WriteI32(env, size_offset, result.required_size);
      WriteI32(env, handle_count_offset, result.required_channels);
      results[0].set_i32(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL);
      return wabt::interp::Result::Ok;
    } else if (result.msg == nullptr) {
      LOG(INFO) << "channel_read[" << channel_handle << "]: no message available";
      WriteI32(env, size_offset, 0);
      results[0].set_i32(OakStatus::OK);
      return wabt::interp::Result::Ok;
    }

    LOG(INFO) << "channel_read[" << channel_handle << "]: read message of size "
              << result.msg->data.size() << " with " << result.msg->channels.size()
              << " attached channels";
    WriteI32(env, size_offset, result.msg->data.size());
    WriteMemory(env, offset, absl::Span<char>(result.msg->data.data(), result.msg->data.size()));
    WriteI32(env, handle_count_offset, result.msg->channels.size());

    // Convert any accompanying channels into handles relative to the receiving node.
    for (size_t ii = 0; ii < result.msg->channels.size(); ii++) {
      Handle handle = AddChannel(std::move(result.msg->channels[ii]));
      LOG(INFO) << "Transferred channel has new handle " << handle;
      WriteU64(env, handle_space_offset + 8 * ii, handle);
    }
    results[0].set_i32(OakStatus::OK);

    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback WasmNode::OakChannelWrite(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    Handle channel_handle = args[0].get_i64();
    uint32_t offset = args[1].get_i32();
    uint32_t size = args[2].get_i32();
    uint32_t handle_offset = args[3].get_i32();
    uint32_t handle_count = args[4].get_i32();

    // Borrowing a reference to the channel is safe because the Node is single
    // threaded and so cannot invoke channel_close while channel_write is
    // ongoing.
    MessageChannelWriteHalf* channel = BorrowWriteChannel(channel_handle);
    if (channel == nullptr) {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
      results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
      return wabt::interp::Result::Ok;
    }

    // Copy the data from the Wasm linear memory.
    absl::Span<const char> origin = ReadMemory(env, offset, size);
    auto msg = absl::make_unique<Message>();
    msg->data.insert(msg->data.end(), origin.begin(), origin.end());
    LOG(INFO) << "channel_write[" << channel_handle << "]: write message of size " << size;

    // Find any handles and clone the corresponding write channels.
    std::vector<Handle> handles;
    handles.reserve(handle_count);
    for (uint32_t ii = 0; ii < handle_count; ii++) {
      Handle handle = ReadU64(env, handle_offset + (8 * ii));
      LOG(INFO) << "Transfer channel handle " << handle;
      ChannelHalf* half = BorrowChannel(handle);
      if (half == nullptr) {
        LOG(WARNING) << "Invalid transferred channel handle: " << handle;
        results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
        return wabt::interp::Result::Ok;
      }
      msg->channels.push_back(CloneChannelHalf(half));
    }

    channel->Write(std::move(msg));
    results[0].set_i32(OakStatus::OK);

    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback WasmNode::OakWaitOnChannels(wabt::interp::Environment* env) {
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

    std::vector<std::unique_ptr<ChannelStatus>> statuses;
    statuses.reserve(count);
    for (uint32_t ii = 0; ii < count; ii++) {
      uint64_t handle = ReadU64(env, offset + (9 * ii));
      statuses.push_back(absl::make_unique<ChannelStatus>(handle));
    }
    auto space = env->GetMemory(0)->data.begin() + offset;
    if (WaitOnChannels(&statuses)) {
      // Transcribe the ready bits into the notification space.
      for (uint32_t ii = 0; ii < count; ii++) {
        if (statuses[ii]->ready) {
          auto base = space + (9 * ii);
          base[8] = 0x01;
        }
      }
    } else {
      results[0].set_i32(OakStatus::ERR_CHANNEL_CLOSED);
    }
    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback WasmNode::OakChannelCreate(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    uint32_t write_half_offset = args[0].get_i32();
    uint32_t read_half_offset = args[1].get_i32();
    results[0].set_i32(OakStatus::OK);

    MessageChannel::ChannelHalves halves = MessageChannel::Create();
    Handle write_handle = AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.write)));
    Handle read_handle = AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.read)));
    LOG(INFO) << "Created new channel with handles write=" << write_handle
              << ", read=" << read_handle;

    WriteU64(env, write_half_offset, write_handle);
    WriteU64(env, read_half_offset, read_handle);

    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback WasmNode::OakChannelClose(wabt::interp::Environment* env) {
  return [this](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    Handle channel_handle = args[0].get_i64();

    if (CloseChannel(channel_handle)) {
      LOG(INFO) << "Closed channel handle: " << channel_handle;
      results[0].set_i32(OakStatus::OK);
    } else {
      LOG(WARNING) << "Invalid channel handle: " << channel_handle;
      results[0].set_i32(OakStatus::ERR_BAD_HANDLE);
    }
    return wabt::interp::Result::Ok;
  };
}

wabt::interp::HostFunc::Callback WasmNode::OakChannelFind(wabt::interp::Environment* env) {
  return [this, env](const wabt::interp::HostFunc* func, const wabt::interp::FuncSignature* sig,
                     const wabt::interp::TypedValues& args, wabt::interp::TypedValues& results) {
    LogHostFunctionCall(func, args);

    uint32_t offset = args[0].get_i32();
    uint32_t length = args[1].get_i32();

    auto base = env->GetMemory(0)->data.begin() + offset;
    std::string port_name(base, base + length);

    Handle handle = FindChannel(port_name);
    results[0].set_i64(handle);  // zero if not found

    return wabt::interp::Result::Ok;
  };
}

}  // namespace oak

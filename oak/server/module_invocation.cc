/*
 * Copyright 2019 The Project Oak Authors
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

#include "oak/server/module_invocation.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/server/channel.h"

namespace oak {

namespace {

// Copy the data from a gRPC ByteBuffer into a Message.
std::unique_ptr<Message> Unwrap(const grpc::ByteBuffer& buffer) {
  std::vector<::grpc::Slice> slices;
  grpc::Status status = buffer.Dump(&slices);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not unwrap buffer";
  }
  std::unique_ptr<Message> bytes = absl::make_unique<Message>();
  for (const auto& slice : slices) {
    bytes->insert(bytes->end(), slice.begin(), slice.end());
  }
  return bytes;
}

}  // namespace

void ModuleInvocation::Start() {
  auto* callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ReadRequest, this, std::placeholders::_1));
  service_->RequestCall(&context_, &stream_, queue_, queue_, callback);
}

void ModuleInvocation::ReadRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  auto* callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ProcessRequest, this, std::placeholders::_1));
  stream_.Read(&request_, callback);
}

void ModuleInvocation::ProcessRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  std::unique_ptr<Message> request_data = Unwrap(request_);

  grpc::Status status = node_->ProcessModuleInvocation(&context_, std::move(request_data));
  if (!status.ok()) {
    FinishAndRestart(status);
    return;
  }

  // Move straight onto sending first response.
  SendResponse(true);
}

void ModuleInvocation::SendResponse(bool ok) {
  if (!ok) {
    delete this;
    return;
  }

  oak::GrpcResponse grpc_out = node_->NextResponse();
  if (grpc_out.status().code() != grpc::StatusCode::OK) {
    LOG(WARNING) << "Encapsulated response has non-OK status: " << grpc_out.status().code();
    // Assume google::rpc::Status maps directly to grpc::Status.
    FinishAndRestart(grpc::Status(static_cast<grpc::StatusCode>(grpc_out.status().code()),
                                  grpc_out.status().message()));
    return;
  }

  const grpc::string& inner_msg = grpc_out.rsp_msg().value();
  grpc::Slice slice(inner_msg.data(), inner_msg.size());
  grpc::ByteBuffer bb(&slice, /*nslices=*/1);

  grpc::WriteOptions options;
  if (!grpc_out.last()) {
    LOG(INFO) << "Non-final inner response of size " << inner_msg.size();
    auto* callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::SendResponse, this, std::placeholders::_1));
    stream_.Write(bb, options, callback);
  } else if (!grpc_out.has_rsp_msg()) {
    // Final iteration but no response, just Finish.
    LOG(INFO) << "Final inner response empty";
    FinishAndRestart(::grpc::Status::OK);
  } else {
    // Final response, so WriteAndFinish then kick off the next round.
    LOG(INFO) << "Final inner response of size " << inner_msg.size();
    options.set_last_message();
    auto* callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
    stream_.WriteAndFinish(bb, options, ::grpc::Status::OK, callback);

    // Restart the gRPC flow with a new ModuleInvocation object for the next request
    // after processing this request.  This ensures that processing is serialized.
    auto* request = new ModuleInvocation(service_, queue_, node_);
    request->Start();
  }
}

void ModuleInvocation::Finish(bool ok) { delete this; }

void ModuleInvocation::FinishAndRestart(const grpc::Status& status) {
  // Restart the gRPC flow with a new ModuleInvocation object for the next request
  // after processing this request.  This ensures that processing is serialized.
  auto* request = new ModuleInvocation(service_, queue_, node_);
  request->Start();

  // Finish the current invocation (which triggers self-destruction).
  auto* callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
  stream_.Finish(status, callback);
}

}  // namespace oak

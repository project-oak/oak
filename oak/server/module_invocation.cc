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
  auto bytes = absl::make_unique<Message>();
  for (const auto& slice : slices) {
    bytes->insert(bytes->end(), slice.begin(), slice.end());
  }
  return bytes;
}

}  // namespace

void ModuleInvocation::Start() {
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ReadRequest, this, std::placeholders::_1));
  service_->RequestCall(&context_, &stream_, queue_, queue_, callback);
}

void ModuleInvocation::ReadRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ProcessRequest, this, std::placeholders::_1));
  stream_.Read(&request_, callback);
}

void ModuleInvocation::ProcessRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  std::unique_ptr<Message> request_data = Unwrap(request_);

  LOG(INFO) << "Handling gRPC call: " << context_.method();

  // Build an encapsulation of the gRPC request invocation and write its serialized
  // form to the gRPC input channel.
  oak::GrpcRequest grpc_request;
  grpc_request.set_method_name(context_.method());
  google::protobuf::Any* any = new google::protobuf::Any();
  any->set_value(request_data->data(), request_data->size());
  grpc_request.set_allocated_req_msg(any);
  grpc_request.set_last(true);
  std::string encap_req;
  grpc_request.SerializeToString(&encap_req);
  // TODO: figure out a way to avoid the extra copy (into then out of std::string)
  std::unique_ptr<Message> encap_data =
      absl::make_unique<Message>(encap_req.begin(), encap_req.end());
  // Write data to the gRPC input channel, which the runtime connected to the
  // Node.
  req_half_->Write(std::move(encap_data));
  LOG(INFO) << "Wrote encapsulated request to gRPC input channel";

  // Move straight onto sending first response.
  SendResponse(true);
}

void ModuleInvocation::SendResponse(bool ok) {
  if (!ok) {
    delete this;
    return;
  }

  ReadResult rsp_result;
  // Block until we can read a single queued GrpcResponse message (in serialized form) from the
  // gRPC output channel.
  rsp_result = rsp_half_->BlockingRead(INT_MAX);
  if (rsp_result.required_size > 0) {
    LOG(ERROR) << "Message size too large: " << rsp_result.required_size;
    FinishAndRestart(grpc::Status(grpc::StatusCode::INTERNAL, "Message size too large"));
    return;
  }

  LOG(INFO) << "Read encapsulated message of size " << rsp_result.data->size()
            << " from gRPC output channel";
  oak::GrpcResponse grpc_response;
  // TODO: Check errors.
  grpc_response.ParseFromString(std::string(rsp_result.data->data(), rsp_result.data->size()));

  const grpc::string& inner_msg = grpc_response.rsp_msg().value();
  grpc::Slice slice(inner_msg.data(), inner_msg.size());
  grpc::ByteBuffer bb(&slice, /*nslices=*/1);

  grpc::WriteOptions options;
  if (!grpc_response.last()) {
    LOG(INFO) << "Non-final inner response of size " << inner_msg.size();
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::SendResponse, this, std::placeholders::_1));
    stream_.Write(bb, options, callback);
  } else if (!grpc_response.has_rsp_msg()) {
    // Final iteration but no response, just Finish.
    LOG(INFO) << "Final inner response empty";
    FinishAndRestart(::grpc::Status::OK);
  } else {
    // Final response, so WriteAndFinish then kick off the next round.
    LOG(INFO) << "Final inner response of size " << inner_msg.size();
    options.set_last_message();
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
    stream_.WriteAndFinish(bb, options, ::grpc::Status::OK, callback);

    // Restart the gRPC flow with a new ModuleInvocation object for the next request
    // after processing this request.  This ensures that processing is serialized.
    auto request = new ModuleInvocation(service_, queue_, req_half_, rsp_half_);
    request->Start();
  }
}

void ModuleInvocation::Finish(bool ok) { delete this; }

void ModuleInvocation::FinishAndRestart(const grpc::Status& status) {
  // Restart the gRPC flow with a new ModuleInvocation object for the next request
  // after processing this request.  This ensures that processing is serialized.
  auto request = new ModuleInvocation(service_, queue_, req_half_, rsp_half_);
  request->Start();

  // Finish the current invocation (which triggers self-destruction).
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
  stream_.Finish(status, callback);
}

}  // namespace oak

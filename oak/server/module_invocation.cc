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
#include "oak/common/policy.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/proto/policy.pb.h"
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
  auto msg = absl::make_unique<Message>();
  for (const auto& slice : slices) {
    msg->data.insert(msg->data.end(), slice.begin(), slice.end());
  }
  return msg;
}

}  // namespace

void ModuleInvocation::Start() {
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ReadRequest, this, std::placeholders::_1));
  LOG(INFO) << "invocation#" << stream_id_ << " Start: request service->RequestCall => ReadRequest";
  service_->RequestCall(&context_, &stream_, queue_, queue_, callback);
}

void ModuleInvocation::ReadRequest(bool ok) {
  if (!ok) {
    LOG(INFO) << "invocation#" << stream_id_ << " ReadRequest: not OK, terminating";
    delete this;
    return;
  }
  LOG(INFO) << "invocation#" << stream_id_
            << " ReadRequest: request stream->Read => ProcessRequest";
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::ProcessRequest, this, std::placeholders::_1));
  stream_.Read(&request_, callback);

  // Now that processing of this request has started, start watching out for the
  // next request.
  LOG(INFO) << "invocation#" << stream_id_ << " start next invocation";
  auto next_invocation = new ModuleInvocation(service_, queue_, grpc_node_);
  next_invocation->Start();
}

void ModuleInvocation::ProcessRequest(bool ok) {
  if (!ok) {
    LOG(INFO) << "invocation#" << stream_id_ << " ProcessRequest: not OK, terminating";
    delete this;
    return;
  }
  std::unique_ptr<Message> request_msg = Unwrap(request_);

  LOG(INFO) << "invocation#" << stream_id_
            << " ProcessRequest: handling gRPC call: " << context_.method();
  for (auto entry : context_.client_metadata()) {
    auto key = entry.first;
    auto value = entry.second;
    // Redact authorization bearer tokens.
    if (key == kOakAuthorizationBearerTokenGrpcMetadataKey) {
      value = "<redacted>";
    }
    LOG(INFO) << "invocation#" << stream_id_ << " gRPC client metadata: [" << key << "] -> ["
              << value << "]";
  }

  // Build an encapsulation of the gRPC request invocation and write its serialized
  // form to the gRPC input channel.
  oak::GrpcRequest grpc_request;
  grpc_request.set_method_name(context_.method());
  google::protobuf::Any* any = new google::protobuf::Any();
  any->set_value(request_msg->data.data(), request_msg->data.size());
  grpc_request.set_allocated_req_msg(any);
  grpc_request.set_last(true);
  std::string encap_req;
  grpc_request.SerializeToString(&encap_req);
  // TODO: figure out a way to avoid the extra copy (into then out of std::string)
  std::unique_ptr<Message> req_msg = absl::make_unique<Message>();
  req_msg->data.insert(req_msg->data.end(), encap_req.begin(), encap_req.end());
  {
    auto range = context_.client_metadata().equal_range(kOakPolicyGrpcMetadataKey);
    for (auto entry = range.first; entry != range.second; ++entry) {
      std::string policy_base64(entry->second.data(), entry->second.size());
      oak::policy::Labels policy = DeserializePolicy(policy_base64);
      // TODO(https://github.com/project-oak/oak/issues/306): Note that at the moment policies may
      // refer to authentication bearer tokens, which if logged in this way may be reused by
      // unauthorized parties. For now we are fine with this, eventually bearer tokens will be
      // removed and replaced by public key assertions, in which case it will always be safe to log
      // policies.
      LOG(INFO) << "invocation#" << stream_id_ << " Oak policy: " << policy.DebugString();
      req_msg->labels = policy;
    }
  }
  {
    // TODO: Provide capability to declassify data for any authorization token provided.
    auto range =
        context_.client_metadata().equal_range(kOakAuthorizationBearerTokenGrpcMetadataKey);
    for (auto entry = range.first; entry != range.second; ++entry) {
      // Redact authorization bearer tokens.
      LOG(INFO) << "invocation#" << stream_id_ << " Oak Authorization Token: <redacted>";
    }
  }

  // Create a channel for responses to this particular method invocation, and
  // attach the write half to the message.
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  rsp_half_ = std::move(halves.read);
  auto bare_half = absl::make_unique<ChannelHalf>(std::move(halves.write));
  req_msg->channels.push_back(std::move(bare_half));

  // Write data to the gRPC input channel, which the runtime connected to the
  // Node.
  MessageChannelWriteHalf* req_half = grpc_node_->BorrowWriteChannel();
  req_half->Write(std::move(req_msg));
  LOG(INFO) << "invocation#" << stream_id_
            << " ProcessRequest: Wrote encapsulated request to gRPC input channel";

  // Move straight onto sending first response.
  SendResponse(true);
}

void ModuleInvocation::SendResponse(bool ok) {
  if (!ok) {
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: not OK, terminating";
    delete this;
    return;
  }

  // Do the work of sending a response in a separate thread, because we may
  // need to block (to wait for a streaming server response) and don't want
  // to hold up the main completion queue thread.
  std::thread other([this] { BlockingSendResponse(); });
  other.detach();
}

void ModuleInvocation::BlockingSendResponse() {
  ReadResult rsp_result;
  // Block until we can read a single queued GrpcResponse message (in serialized form) from the
  // gRPC output channel.
  LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: do blocking-read on grpc channel";
  rsp_result = rsp_half_->BlockingRead(INT_MAX, INT_MAX);
  if (rsp_result.required_size > 0) {
    LOG(ERROR) << "invocation#" << stream_id_
               << " SendResponse: Message size too large: " << rsp_result.required_size;
    FinishAndRestart(grpc::Status(grpc::StatusCode::INTERNAL, "Message size too large"));
    return;
  }

  LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Read encapsulated message of size "
            << rsp_result.msg->data.size() << " from gRPC output channel";
  oak::GrpcResponse grpc_response;
  // TODO: Check errors.
  grpc_response.ParseFromString(
      std::string(rsp_result.msg->data.data(), rsp_result.msg->data.size()));
  // Any channel references included with the message will be dropped.

  const grpc::string& inner_msg = grpc_response.rsp_msg().value();
  grpc::Slice slice(inner_msg.data(), inner_msg.size());
  grpc::ByteBuffer bb(&slice, /*nslices=*/1);

  grpc::WriteOptions options;
  if (!grpc_response.last()) {
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Non-final inner response of size "
              << inner_msg.size() << ", request stream->Write => SendResponse";
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::SendResponse, this, std::placeholders::_1));
    stream_.Write(bb, options, callback);
  } else if (!grpc_response.has_rsp_msg()) {
    // Final iteration but no response, just Finish.
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Final inner response empty";
    FinishAndRestart(::grpc::Status::OK);
  } else {
    // Final response, so WriteAndFinish then kick off the next round.
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Final inner response of size "
              << inner_msg.size() << ", request stream->WriteAndFinish => Finish";
    options.set_last_message();
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
    stream_.WriteAndFinish(bb, options, ::grpc::Status::OK, callback);
  }
}

void ModuleInvocation::Finish(bool ok) {
  LOG(INFO) << "invocation#" << stream_id_ << " Finish: delete self";
  delete this;
}

void ModuleInvocation::FinishAndRestart(const grpc::Status& status) {
  // Finish the current invocation (which triggers self-destruction).
  LOG(INFO) << "invocation#" << stream_id_
            << "  FinishAndRestart: request stream->Finish => Finish";
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::Finish, this, std::placeholders::_1));
  stream_.Finish(status, callback);
}

}  // namespace oak

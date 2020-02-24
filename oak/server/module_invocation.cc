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

  // Build an encapsulation of the gRPC request invocation and put it in a Message.
  oak::GrpcRequest grpc_request;
  grpc_request.set_method_name(context_.method());
  google::protobuf::Any* any = new google::protobuf::Any();
  any->set_value(request_msg->data.data(), request_msg->data.size());
  grpc_request.set_allocated_req_msg(any);
  grpc_request.set_last(true);

  std::unique_ptr<Message> req_msg = absl::make_unique<Message>();
  size_t serialized_size = grpc_request.ByteSizeLong();
  req_msg->data.resize(serialized_size);
  grpc_request.SerializeToArray(req_msg->data.data(), req_msg->data.size());
  {
    auto range = context_.client_metadata().equal_range(kOakPolicyGrpcMetadataKey);
    for (auto entry = range.first; entry != range.second; ++entry) {
      std::string policy_base64(entry->second.data(), entry->second.size());
      oak::policy::Label policy = DeserializePolicy(policy_base64);
      // TODO(https://github.com/project-oak/oak/issues/306): Note that at the moment policies may
      // refer to authentication bearer tokens, which if logged in this way may be reused by
      // unauthorized parties. For now we are fine with this, eventually bearer tokens will be
      // removed and replaced by public key assertions, in which case it will always be safe to log
      // policies.
      LOG(INFO) << "invocation#" << stream_id_ << " Oak policy: " << policy.DebugString();
      req_msg->label = policy;
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

  // Create a pair of channels for communication corresponding to this
  // particular method invocation, one for sending in requests, and one for
  // receiving responses.
  MessageChannel::ChannelHalves req_halves = MessageChannel::Create();
  req_half_ = std::move(req_halves.write);
  MessageChannel::ChannelHalves rsp_halves = MessageChannel::Create();
  rsp_half_ = std::move(rsp_halves.read);

  // Build a notification message that just holds references to these two
  // newly-created channels.
  std::unique_ptr<Message> notify_msg = absl::make_unique<Message>();
  notify_msg->channels.push_back(absl::make_unique<ChannelHalf>(std::move(req_halves.read)));
  notify_msg->channels.push_back(absl::make_unique<ChannelHalf>(std::move(rsp_halves.write)));

  // Write the request message to the just-created request channel.
  req_half_->Write(std::move(req_msg));
  LOG(INFO) << "invocation#" << stream_id_
            << " ProcessRequest: Wrote encapsulated request to new gRPC request channel";

  // Write the notification message to the gRPC input channel, which the runtime
  // connected to the Node.
  MessageChannelWriteHalf* notify_half = grpc_node_->BorrowWriteChannel();
  notify_half->Write(std::move(notify_msg));
  LOG(INFO) << "invocation#" << stream_id_
            << " ProcessRequest: Wrote notification request to gRPC input channel";

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
    FinishAndCleanUp(grpc::Status(grpc::StatusCode::INTERNAL, "Message size too large"));
    return;
  }

  LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Read encapsulated message of size "
            << rsp_result.msg->data.size() << " from gRPC output channel";
  oak::GrpcResponse grpc_response;
  if (!grpc_response.ParseFromString(
          std::string(rsp_result.msg->data.data(), rsp_result.msg->data.size()))) {
    LOG(ERROR) << "invocation#" << stream_id_
               << " SendResponse: failed to parse encapsulated message";
    FinishAndCleanUp(grpc::Status(grpc::StatusCode::INTERNAL, "Message failed to parse"));
    return;
  }
  // Any channel references included with the message will be dropped.

  const grpc::string& inner_msg = grpc_response.rsp_msg().value();
  grpc::Slice slice(inner_msg.data(), inner_msg.size());
  grpc::ByteBuffer bb(&slice, /*nslices=*/1);

  grpc::WriteOptions options;
  if (!grpc_response.last()) {
    // More response data is expected, so queue up another SendResponse action.
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Non-final inner response of size "
              << inner_msg.size() << ", request stream->Write => SendResponse";
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::SendResponse, this, std::placeholders::_1));
    stream_.Write(bb, options, callback);
  } else if (!grpc_response.has_rsp_msg()) {
    // Final iteration but no response, just Finish.
    google::rpc::Status status = grpc_response.status();
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Final inner response empty, status "
              << status.code();
    FinishAndCleanUp(grpc::Status(static_cast<grpc::StatusCode>(status.code()), status.message()));
  } else {
    // Final response, so WriteAndFinish.
    LOG(INFO) << "invocation#" << stream_id_ << " SendResponse: Final inner response of size "
              << inner_msg.size() << ", request stream->WriteAndFinish => CleanUp";
    options.set_last_message();
    auto callback = new std::function<void(bool)>(
        std::bind(&ModuleInvocation::CleanUp, this, std::placeholders::_1));
    stream_.WriteAndFinish(bb, options, ::grpc::Status::OK, callback);
  }
}

void ModuleInvocation::CleanUp(bool /*ok*/) {
  LOG(INFO) << "invocation#" << stream_id_ << " CleanUp: delete self";
  delete this;
}

void ModuleInvocation::FinishAndCleanUp(const grpc::Status& status) {
  // Finish the current invocation (which triggers self-destruction).
  LOG(INFO) << "invocation#" << stream_id_
            << " FinishAndCleanUp: request stream->Finish => CleanUp";
  auto callback = new std::function<void(bool)>(
      std::bind(&ModuleInvocation::CleanUp, this, std::placeholders::_1));
  stream_.Finish(status, callback);
}

}  // namespace oak

/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/server/grpc_client_node.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
#include "oak/proto/grpc_encap.pb.h"

namespace oak {

namespace {
// Convert an integer to a void* for tagging completion queue steps.
void* tag(int i) { return (void*)static_cast<intptr_t>(i); }
}  // namespace

GrpcClientNode::GrpcClientNode(BaseRuntime* runtime, const std::string& name,
                               const std::string& grpc_address)
    : NodeThread(runtime, name),
      channel_(grpc::CreateChannel(grpc_address, grpc::InsecureChannelCredentials())),
      stub_(new grpc::GenericStub(channel_)) {
  LOG(INFO) << "Created gRPC client node for " << grpc_address;
}

bool GrpcClientNode::HandleInvocation(MessageChannelReadHalf* invocation_channel) {
  // Expect to receive a pair of handles:
  //  - Handle to the read half of a channel that holds the request, serialized
  //    as a GrpcRequest.
  //  - Handle to the write half of a channel to send responses down, each
  //    serialized as a GrpcResponse.
  ReadResult invocation = invocation_channel->Read(INT_MAX, INT_MAX);
  if (invocation.required_size > 0) {
    LOG(ERROR) << "Message size too large: " << invocation.required_size;
    return false;
  }
  if (invocation.msg->data.size() != 0) {
    LOG(ERROR) << "Unexpectedly received data in invocation";
    return false;
  }
  if (invocation.msg->channels.size() != 2) {
    LOG(ERROR) << "Wrong number of channels " << invocation.msg->channels.size()
               << " in invocation";
    return false;
  }

  std::unique_ptr<ChannelHalf> half0 = std::move(invocation.msg->channels[0]);
  auto channel0 = absl::get_if<std::unique_ptr<MessageChannelReadHalf>>(half0.get());
  if (channel0 == nullptr) {
    LOG(ERROR) << "First channel accompanying invocation is write-direction";
    return false;
  }
  std::unique_ptr<MessageChannelReadHalf> req_channel = std::move(*channel0);

  std::unique_ptr<ChannelHalf> half1 = std::move(invocation.msg->channels[1]);
  auto channel1 = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half1.get());
  if (channel1 == nullptr) {
    LOG(ERROR) << "Second channel accompanying invocation is read-direction";
    return false;
  }
  std::unique_ptr<MessageChannelWriteHalf> rsp_channel = std::move(*channel1);

  // Expect to read a single request out of the request channel.
  // TODO(#97): support client-side streaming
  ReadResult req_result = req_channel->Read(INT_MAX, INT_MAX);
  if (req_result.required_size > 0) {
    LOG(ERROR) << "Message size too large: " << req_result.required_size;
    return false;
  }
  if (req_result.msg->channels.size() != 0) {
    LOG(ERROR) << "Unexpectedly received channel handles in request channel";
    return false;
  }
  GrpcRequest grpc_req;
  grpc_req.ParseFromString(std::string(req_result.msg->data.data(), req_result.msg->data.size()));
  std::string method_name = grpc_req.method_name();
  const grpc::string& req_data = grpc_req.req_msg().value();

  // Use a completion queue together with a generic client reader/writer to
  // perform the method invocation.  All steps are done in serial, so just use
  // consecutive integer values for completion queue tags (there's no need to
  // use the tag values for correlation). Inspired by:
  // https://github.com/grpc/grpc/blob/master/test/cpp/util/cli_call.cc
  LOG(INFO) << "Invoke method " << method_name;
  grpc::ClientContext ctx;
  grpc::CompletionQueue cq;
  std::unique_ptr<grpc::GenericClientAsyncReaderWriter> call =
      stub_->PrepareCall(&ctx, method_name, &cq);
  call->StartCall(tag(1));

  void* got_tag;
  bool ok;
  cq.Next(&got_tag, &ok);
  if (!ok) {
    LOG(ERROR) << "Failed to start gRPC method call";
    return false;
  }

  // Send the un-encapsulated gRPC request (which is already serialized).
  grpc::Slice slice(req_data.data(), req_data.size());
  grpc::ByteBuffer send_bb(&slice, /*nslices=*/1);
  call->Write(send_bb, tag(2));
  cq.Next(&got_tag, &ok);
  if (!ok) {
    LOG(ERROR) << "Failed to send gRPC request";
    return false;
  }
  call->WritesDone(tag(3));
  cq.Next(&got_tag, &ok);
  if (!ok) {
    LOG(ERROR) << "Failed to close gRPC request";
    return false;
  }

  // Loop round reading responses off the completion queue (which allows for
  // server-streaming gRPC methods).
  while (true) {
    grpc::ByteBuffer recv_bb;
    call->Read(&recv_bb, tag(4));
    if (!cq.Next(&got_tag, &ok) || !ok) {
      LOG(INFO) << "No next gRPC response";
      break;
    }
    std::vector<grpc::Slice> rsp_slices;
    recv_bb.Dump(&rsp_slices);
    grpc::string rsp_data;
    for (size_t i = 0; i < rsp_slices.size(); i++) {
      rsp_data.append(reinterpret_cast<const char*>(rsp_slices[i].begin()), rsp_slices[i].size());
    }

    // Build an encapsulation of the gRPC response and put it in an Oak Message.
    oak::GrpcResponse grpc_rsp;
    grpc_rsp.set_last(false);
    google::protobuf::Any* any = new google::protobuf::Any();
    any->set_value(rsp_data.data(), rsp_data.size());
    grpc_rsp.set_allocated_rsp_msg(any);

    std::unique_ptr<Message> rsp_msg = absl::make_unique<Message>();
    size_t serialized_size = grpc_rsp.ByteSizeLong();
    rsp_msg->data.resize(serialized_size);
    grpc_rsp.SerializeToArray(rsp_msg->data.data(), rsp_msg->data.size());

    // Write the encapsulated response Message to the response channel.
    LOG(INFO) << "Write gRPC response message to response channel";
    rsp_channel->Write(std::move(rsp_msg));
  }

  LOG(INFO) << "Finish invocation method " << method_name;
  grpc::Status status;
  call->Finish(&status, tag(5));
  cq.Next(&got_tag, &ok);
  if (!ok) {
    LOG(ERROR) << "Failed to finish gRPC method invocation";
  }

  // References to the per-invocation request/response channels will be dropped
  // on exit, orphaning them.
  return true;
}

void GrpcClientNode::Run(Handle invocation_handle) {
  // Borrow a pointer to the relevant channel half.
  MessageChannelReadHalf* invocation_channel = BorrowReadChannel(invocation_handle);
  if (invocation_channel == nullptr) {
    LOG(ERROR) << "Required channel not available; handle: " << invocation_handle;
    return;
  }
  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(invocation_handle));
  while (true) {
    if (!WaitOnChannels(&channel_status)) {
      LOG(WARNING) << "Node termination requested";
      return;
    }

    if (!HandleInvocation(invocation_channel)) {
      LOG(ERROR) << "Invocation processing failed";
      return;
    }
  }
  // Drop reference to the invocation channel on exit.
}

}  // namespace oak

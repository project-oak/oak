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

#include "oak/server/storage/storage_node.h"

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "asylo/util/cleansing_types.h"
#include "asylo/util/logging.h"
#include "asylo/util/status_macros.h"
#include "grpcpp/create_channel.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/proto/storage_channel.pb.h"

namespace oak {

StorageNode::StorageNode(BaseRuntime* runtime, const std::string& name,
                         const std::string& storage_address)
    : NodeThread(runtime, name), storage_processor_(storage_address) {}

void StorageNode::Run(Handle request_handle) {
  // Borrow a pointer to the relevant channel half.
  MessageChannelReadHalf* request_channel = BorrowReadChannel(request_handle);
  if (request_channel == nullptr) {
    LOG(ERROR) << "Required channel not available; handle: " << request_handle;
    return;
  }
  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(request_handle));
  while (true) {
    if (!WaitOnChannels(&channel_status)) {
      LOG(WARNING) << "Node termination requested";
      return;
    }

    ReadResult result = request_channel->Read(INT_MAX, INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }

    // Expect to receive a request (as serialized data) and the write half of a
    // channel to send responses on.
    if (result.msg->channels.size() == 0) {
      LOG(ERROR) << "No response channel accompanying storage request";
      return;
    }
    std::unique_ptr<ChannelHalf> half = std::move(result.msg->channels[0]);
    auto channel = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half.get());
    if (channel == nullptr) {
      LOG(ERROR) << "Channel accompanying storage request is read-direction";
      return;
    }
    std::unique_ptr<MessageChannelWriteHalf> response_channel = std::move(*channel);
    GrpcRequest channel_request;
    channel_request.ParseFromString(std::string(result.msg->data.data(), result.msg->data.size()));

    std::unique_ptr<GrpcResponse> channel_response;
    asylo::StatusOr<std::unique_ptr<GrpcResponse>> rsp_or = ProcessMethod(&channel_request);
    if (!rsp_or.ok()) {
      LOG(ERROR) << "Failed to perform " << channel_request.method_name() << ": "
                 << rsp_or.status().error_code() << ", '" << rsp_or.status().error_message() << "'";
      channel_response = absl::make_unique<GrpcResponse>();
      channel_response->mutable_status()->set_code(rsp_or.status().error_code());
      channel_response->mutable_status()->set_message(std::string(rsp_or.status().error_message()));
    } else {
      channel_response = std::move(rsp_or).ValueOrDie();
    }

    std::string response_data;
    channel_response->SerializeToString(&response_data);
    // TODO: figure out a way to avoid the extra copy (into then out of
    // std::string)
    std::unique_ptr<Message> response_message = absl::make_unique<Message>();
    response_message->data.insert(response_message->data.end(), response_data.begin(),
                                  response_data.end());
    response_channel->Write(std::move(response_message));

    // The response channel reference is dropped here.
  }
}

asylo::StatusOr<std::unique_ptr<GrpcResponse>> StorageNode::ProcessMethod(
    GrpcRequest* channel_request) {
  auto channel_response = absl::make_unique<GrpcResponse>();
  grpc::Status status;
  std::string method_name = channel_request->method_name();
  if (method_name == "/oak.StorageNode/Read") {
    StorageChannelReadRequest channel_read_request;
    if (!channel_request->req_msg().UnpackTo(&channel_read_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    StorageChannelReadResponse channel_read_response;
    std::string value;
    ASYLO_ASSIGN_OR_RETURN(value, storage_processor_.Read(channel_read_request.storage_name(),
                                                          channel_read_request.item().name(),
                                                          channel_read_request.transaction_id()));
    channel_read_response.mutable_item()->ParseFromString(value);
    // TODO(#449): Check security policy for item.
    channel_response->mutable_rsp_msg()->PackFrom(channel_read_response);
  } else if (method_name == "/oak.StorageNode/Write") {
    StorageChannelWriteRequest channel_write_request;
    if (!channel_request->req_msg().UnpackTo(&channel_write_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    // TODO(#449): Check integrity policy for item.
    std::string item;
    channel_write_request.item().SerializeToString(&item);
    ASYLO_RETURN_IF_ERROR(storage_processor_.Write(channel_write_request.storage_name(),
                                                   channel_write_request.item().name(), item,
                                                   channel_write_request.transaction_id()));
  } else if (method_name == "/oak.StorageNode/Delete") {
    StorageChannelDeleteRequest channel_delete_request;
    if (!channel_request->req_msg().UnpackTo(&channel_delete_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    // TODO(#449): Check integrity policy for item.
    ASYLO_RETURN_IF_ERROR(storage_processor_.Delete(channel_delete_request.storage_name(),
                                                    channel_delete_request.item().name(),
                                                    channel_delete_request.transaction_id()));
  } else if (method_name == "/oak.StorageNode/Begin") {
    StorageChannelBeginRequest channel_begin_request;
    if (!channel_request->req_msg().UnpackTo(&channel_begin_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    StorageChannelBeginResponse channel_begin_response;
    std::string transaction_id;
    ASYLO_ASSIGN_OR_RETURN(transaction_id,
                           storage_processor_.Begin(channel_begin_request.storage_name()));
    channel_begin_response.set_transaction_id(transaction_id);
    channel_response->mutable_rsp_msg()->PackFrom(channel_begin_response);
  } else if (method_name == "/oak.StorageNode/Commit") {
    StorageChannelCommitRequest channel_commit_request;
    if (!channel_request->req_msg().UnpackTo(&channel_commit_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    ASYLO_RETURN_IF_ERROR(storage_processor_.Commit(channel_commit_request.storage_name(),
                                                    channel_commit_request.transaction_id()));
  } else if (method_name == "/oak.StorageNode/Rollback") {
    StorageChannelRollbackRequest channel_rollback_request;
    if (!channel_request->req_msg().UnpackTo(&channel_rollback_request)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    ASYLO_RETURN_IF_ERROR(storage_processor_.Rollback(channel_rollback_request.storage_name(),
                                                      channel_rollback_request.transaction_id()));
  } else {
    LOG(ERROR) << "unknown operation " << method_name;
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Unknown operation request method.");
  }
  return std::move(channel_response);
}

}  // namespace oak

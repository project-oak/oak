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

#include <functional>

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "asylo/util/cleansing_types.h"
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
#include "oak/common/app_config.h"
#include "oak/proto/escrow_channel.pb.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/proto/storage_channel.pb.h"

namespace oak {

StorageNode::StorageNode(const std::string& name, const std::string& storage_address)
    : NodeThread(name) {
  storage_processor_.reset(new StorageProcessor(
      storage_address,
      std::bind(&StorageNode::GetStorageEncryptionKey, this, std::placeholders::_1)));
}

asylo::StatusOr<asylo::CleansingVector<uint8_t>> StorageNode::GetStorageEncryptionKey(
    const std::string& storage_id) {
  Handle request_handle = FindChannel(kEscrowOutPortName);
  Handle response_handle = FindChannel(kEscrowInPortName);
  MessageChannelWriteHalf* request_channel = BorrowWriteChannel(request_handle);
  MessageChannelReadHalf* response_channel = BorrowReadChannel(response_handle);
  if (request_channel == nullptr || response_channel == nullptr) {
    return asylo::Status(asylo::error::GoogleError::UNAVAILABLE,
                         absl::StrCat("Required channel not available; handles: ", request_handle,
                                      ", ", response_handle));
  }

  EscrowChannelReadRequest escrow_read_request;
  escrow_read_request.set_escrow_name(storage_id);
  GrpcRequest channel_request;
  channel_request.set_method_name("/oak.EscrowNode/Read");
  channel_request.mutable_req_msg()->PackFrom(escrow_read_request);
  std::string request_data;
  channel_request.SerializeToString(&request_data);
  std::unique_ptr<Message> request_message = absl::make_unique<Message>();
  request_message->data.insert(request_message->data.end(), request_data.begin(),
                               request_data.end());
  request_channel->Write(std::move(request_message));

  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(response_handle));

  if (!WaitOnChannels(&channel_status)) {
    return asylo::Status(asylo::error::GoogleError::CANCELLED, "Node termination requested");
  }
  ReadResult result = response_channel->Read(INT_MAX, INT_MAX);
  if (result.required_size > 0) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         absl::StrCat("Message size too large: ", result.required_size));
  }

  GrpcResponse channel_response;
  channel_response.ParseFromString(std::string(result.msg->data.data(), result.msg->data.size()));
  EscrowChannelReadResponse escrow_read_response;
  if (!channel_response.rsp_msg().UnpackTo(&escrow_read_response)) {
    return asylo::Status(asylo::error::GoogleError::INTERNAL, "Invalid channel response");
  }
  std::string encryption_key = escrow_read_response.escrow_value();

  return asylo::CleansingVector<uint8_t>(encryption_key.begin(), encryption_key.end());
}

void StorageNode::Run() {
  Handle request_handle = FindChannel(kStorageNodeRequestPortName);
  Handle response_handle = FindChannel(kStorageNodeResponsePortName);
  MessageChannelReadHalf* request_channel = BorrowReadChannel(request_handle);
  MessageChannelWriteHalf* response_channel = BorrowWriteChannel(response_handle);
  if (request_channel == nullptr || response_channel == nullptr) {
    LOG(ERROR) << "Required channel not available; handles: " << request_handle << ", "
               << response_handle;
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

    GrpcRequest channel_request;
    channel_request.ParseFromString(std::string(result.msg->data.data(), result.msg->data.size()));
    GrpcResponse channel_response;
    grpc::Status status;
    std::string method_name = channel_request.method_name();

    if (method_name == "/oak.StorageNode/Read") {
      StorageChannelReadRequest channel_read_request;
      if (!channel_request.req_msg().UnpackTo(&channel_read_request)) {
        // TODO: Handle errors.
      }
      StorageChannelReadResponse channel_read_response;
      storage_processor_->Read(
          channel_read_request.storage_name(), channel_read_request.datum_name(),
          channel_read_request.transaction_id(), channel_read_response.mutable_datum_value());

      channel_response.mutable_rsp_msg()->PackFrom(channel_read_response);
    } else if (method_name == "/oak.StorageNode/Write") {
      StorageChannelWriteRequest channel_write_request;
      if (!channel_request.req_msg().UnpackTo(&channel_write_request)) {
        // TODO: Handle errors.
      }
      storage_processor_->Write(
          channel_write_request.storage_name(), channel_write_request.datum_name(),
          channel_write_request.datum_value(), channel_write_request.transaction_id());
    } else if (method_name == "/oak.StorageNode/Delete") {
      StorageChannelDeleteRequest channel_delete_request;
      if (!channel_request.req_msg().UnpackTo(&channel_delete_request)) {
        // TODO: Handle errors.
      }
      storage_processor_->Delete(channel_delete_request.storage_name(),
                                channel_delete_request.datum_name(),
                                channel_delete_request.transaction_id());
    } else if (method_name == "/oak.StorageNode/Begin") {
      StorageChannelBeginRequest channel_begin_request;
      if (!channel_request.req_msg().UnpackTo(&channel_begin_request)) {
        // TODO: Handle errors.
      }
      StorageChannelBeginResponse channel_begin_response;
      storage_processor_->Begin(channel_begin_request.storage_name(),
                               channel_begin_response.mutable_transaction_id());

      channel_response.mutable_rsp_msg()->PackFrom(channel_begin_response);
    } else if (method_name == "/oak.StorageNode/Commit") {
      StorageChannelCommitRequest channel_commit_request;
      if (!channel_request.req_msg().UnpackTo(&channel_commit_request)) {
        // TODO: Handle errors.
      }
      storage_processor_->Commit(channel_commit_request.storage_name(),
                                channel_commit_request.transaction_id());
    } else if (method_name == "/oak.StorageNode/Rollback") {
      StorageChannelRollbackRequest channel_rollback_request;
      if (!channel_request.req_msg().UnpackTo(&channel_rollback_request)) {
        // TODO: Handle errors.
      }
      storage_processor_->Rollback(channel_rollback_request.storage_name(),
                                  channel_rollback_request.transaction_id());
    } else {
      LOG(ERROR) << "unknown operation";
      status =
          grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Unknown operation request method.");
    }
    if (!status.ok()) {
      LOG(ERROR) << "operation failed: " << status.error_code() << " " << status.error_message();
    }
    channel_response.mutable_status()->set_code(status.error_code());
    channel_response.mutable_status()->set_message(status.error_message());

    std::string response_data;
    channel_response.SerializeToString(&response_data);
    // TODO: figure out a way to avoid the extra copy (into then out of
    // std::string)
    std::unique_ptr<Message> response_message = absl::make_unique<Message>();
    response_message->data.insert(response_message->data.end(), response_data.begin(),
                                  response_data.end());
    response_channel->Write(std::move(response_message));
  }
}

}  // namespace oak

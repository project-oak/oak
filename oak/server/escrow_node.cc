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

#include "oak/server/escrow_node.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "oak/common/app_config.h"
#include "oak/proto/escrow_channel.pb.h"
#include "oak/proto/grpc_encap.pb.h"

namespace oak {

namespace {

std::string GetStorageName() {
  // TODO: Replace with enclave-based ID.
  return "escrow_storage";
}

}  // namespace

EscrowNode::EscrowNode(const std::string& node_name, const std::string& storage_address)
    : NodeThread(node_name) {
  storage_processor_.reset(new StorageProcessor(
      storage_address,
      std::bind(&EscrowNode::GetStorageEncryptionKey, this, std::placeholders::_1)));
}

asylo::StatusOr<asylo::CleansingVector<uint8_t>> EscrowNode::GetStorageEncryptionKey(
    const std::string& storage_id) {
  // TODO: Get enclave hardware key.
  std::string encryption_key =
      absl::HexStringToBytes("c0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedead");
  return asylo::CleansingVector<uint8_t>(encryption_key.begin(), encryption_key.end());
}

// TODO: Refactor common dispatch code.
void EscrowNode::Run() {
  Handle request_handle = FindChannel(kEscrowNodeRequestPortName);
  Handle response_handle = FindChannel(kEscrowNodeResponsePortName);
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
    grpc::Status status;
    GrpcResponse channel_response;
    std::string method_name = channel_request.method_name();

    if (method_name == "/oak.EscrowNode/Read") {
      EscrowChannelReadRequest channel_read_request;
      if (!channel_request.req_msg().UnpackTo(&channel_read_request)) {
        LOG(ERROR) << "Invalid read request";
        // TODO: Handle errors.
      }
      EscrowChannelReadResponse channel_read_response;
      storage_processor_->Read(GetStorageName(), channel_read_request.escrow_name(),
                               /*transaction_id=*/"", channel_read_response.mutable_escrow_value());
      if (channel_read_response.escrow_value().empty()) {
        // TODO: Generate new encryption key for escrow_name and store it.
        channel_read_response.set_escrow_value(absl::HexStringToBytes(
            "c0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedead"));
      }
      channel_response.mutable_rsp_msg()->PackFrom(channel_read_response);
    } else if (method_name == "/oak.EscrowNode/Write") {
      EscrowChannelWriteRequest channel_write_request;
      if (!channel_request.req_msg().UnpackTo(&channel_write_request)) {
        // TODO: Handle errors.
        LOG(ERROR) << "Invalid write request";
      }
      storage_processor_->Write(GetStorageName(), channel_write_request.escrow_name(),
                                channel_write_request.escrow_value(), /*transaction_id=*/"");
    } else if (method_name == "/oak.EscrowNode/Delete") {
      EscrowChannelDeleteRequest channel_delete_request;
      if (!channel_request.req_msg().UnpackTo(&channel_delete_request)) {
        // TODO: Handle errors.
        LOG(ERROR) << "Invalid delete request";
      }
      storage_processor_->Delete(GetStorageName(), channel_delete_request.escrow_name(),
                                 /*transaction_id=*/"");
    } else {
      LOG(ERROR) << "Unknown operation: " << method_name;
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

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

void StorageNode::Run(Handle invocation_handle) {
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

    // Expect to receive a pair of handles in the invocation message:
    //  - Handle to the read half of a channel that holds the request, serialized
    //    as a GrpcRequest.
    //  - Handle to the write half of a channel to send responses down, each
    //    serialized as a GrpcResponse.
    ReadResult invocation = invocation_channel->Read(INT_MAX, INT_MAX);
    if (invocation.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << invocation.required_size;
      return;
    }
    if (invocation.msg->data.size() != 0) {
      LOG(ERROR) << "Unexpectedly received data in invocation";
      return;
    }
    if (invocation.msg->channels.size() != 2) {
      LOG(ERROR) << "Wrong number of channels " << invocation.msg->channels.size()
                 << " in invocation";
      return;
    }

    std::unique_ptr<ChannelHalf> half0 = std::move(invocation.msg->channels[0]);
    auto channel0 = absl::get_if<std::unique_ptr<MessageChannelReadHalf>>(half0.get());
    if (channel0 == nullptr) {
      LOG(ERROR) << "First channel accompanying invocation is write-direction";
      return;
    }
    std::unique_ptr<MessageChannelReadHalf> req_channel = std::move(*channel0);

    std::unique_ptr<ChannelHalf> half1 = std::move(invocation.msg->channels[1]);
    auto channel1 = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half1.get());
    if (channel1 == nullptr) {
      LOG(ERROR) << "Second channel accompanying invocation is read-direction";
      return;
    }
    std::unique_ptr<MessageChannelWriteHalf> rsp_channel = std::move(*channel1);

    // Expect to read a single request out of the request channel.
    ReadResult req_result = req_channel->Read(INT_MAX, INT_MAX);
    if (req_result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << req_result.required_size;
      return;
    }
    if (req_result.msg->channels.size() != 0) {
      LOG(ERROR) << "Unexpectedly received channel handles in request channel";
      return;
    }
    GrpcRequest grpc_req;
    grpc_req.ParseFromString(std::string(req_result.msg->data.data(), req_result.msg->data.size()));

    std::unique_ptr<GrpcResponse> grpc_rsp;
    asylo::StatusOr<std::unique_ptr<GrpcResponse>> rsp_or = ProcessMethod(&grpc_req);
    if (!rsp_or.ok()) {
      LOG(ERROR) << "Failed to perform " << grpc_req.method_name() << ": "
                 << rsp_or.status().error_code() << ", '" << rsp_or.status().error_message() << "'";
      grpc_rsp = absl::make_unique<GrpcResponse>();
      grpc_rsp->mutable_status()->set_code(rsp_or.status().error_code());
      grpc_rsp->mutable_status()->set_message(std::string(rsp_or.status().error_message()));
    } else {
      grpc_rsp = std::move(rsp_or).ValueOrDie();
    }

    grpc_rsp->set_last(true);
    std::unique_ptr<Message> rsp_msg = absl::make_unique<Message>();
    size_t serialized_size = grpc_rsp->ByteSizeLong();
    rsp_msg->data.resize(serialized_size);
    grpc_rsp->SerializeToArray(rsp_msg->data.data(), rsp_msg->data.size());
    rsp_channel->Write(std::move(rsp_msg));

    // The response channel reference is dropped here.
  }
}

asylo::StatusOr<std::unique_ptr<GrpcResponse>> StorageNode::ProcessMethod(GrpcRequest* grpc_req) {
  auto grpc_rsp = absl::make_unique<GrpcResponse>();
  grpc::Status status;
  std::string method_name = grpc_req->method_name();

  if (method_name == "/oak.StorageNode/Read") {
    StorageChannelReadRequest read_req;
    if (!grpc_req->req_msg().UnpackTo(&read_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    StorageChannelReadResponse read_rsp;
    std::string value;
    ASYLO_ASSIGN_OR_RETURN(value,
                           storage_processor_.Read(read_req.storage_name(), read_req.item().name(),
                                                   read_req.transaction_id()));
    read_rsp.mutable_item()->ParseFromString(value);
    // TODO(#449): Check security policy for item.
    grpc_rsp->mutable_rsp_msg()->PackFrom(read_rsp);

  } else if (method_name == "/oak.StorageNode/Write") {
    StorageChannelWriteRequest write_req;
    if (!grpc_req->req_msg().UnpackTo(&write_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    // TODO(#449): Check integrity policy for item.
    std::string item;
    write_req.item().SerializeToString(&item);
    ASYLO_RETURN_IF_ERROR(storage_processor_.Write(
        write_req.storage_name(), write_req.item().name(), item, write_req.transaction_id()));

  } else if (method_name == "/oak.StorageNode/Delete") {
    StorageChannelDeleteRequest delete_req;
    if (!grpc_req->req_msg().UnpackTo(&delete_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    // TODO(#449): Check integrity policy for item.
    ASYLO_RETURN_IF_ERROR(storage_processor_.Delete(
        delete_req.storage_name(), delete_req.item().name(), delete_req.transaction_id()));

  } else if (method_name == "/oak.StorageNode/Begin") {
    StorageChannelBeginRequest begin_req;
    if (!grpc_req->req_msg().UnpackTo(&begin_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    StorageChannelBeginResponse begin_rsp;
    std::string transaction_id;
    ASYLO_ASSIGN_OR_RETURN(transaction_id, storage_processor_.Begin(begin_req.storage_name()));
    begin_rsp.set_transaction_id(transaction_id);
    grpc_rsp->mutable_rsp_msg()->PackFrom(begin_rsp);

  } else if (method_name == "/oak.StorageNode/Commit") {
    StorageChannelCommitRequest commit_req;
    if (!grpc_req->req_msg().UnpackTo(&commit_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    ASYLO_RETURN_IF_ERROR(
        storage_processor_.Commit(commit_req.storage_name(), commit_req.transaction_id()));

  } else if (method_name == "/oak.StorageNode/Rollback") {
    StorageChannelRollbackRequest rollback_req;
    if (!grpc_req->req_msg().UnpackTo(&rollback_req)) {
      return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to unpack request");
    }
    ASYLO_RETURN_IF_ERROR(
        storage_processor_.Rollback(rollback_req.storage_name(), rollback_req.transaction_id()));
  } else {
    LOG(ERROR) << "unknown operation " << method_name;
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Unknown operation request method.");
  }
  return std::move(grpc_rsp);
}

}  // namespace oak

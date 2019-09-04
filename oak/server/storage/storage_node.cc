
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
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
#include "oak/proto/storage_channel.pb.h"

namespace oak {

static std::string GetStorageId(const std::string& storage_name) {
  // TODO: Generate name-based UUID.
  return storage_name;
}

StorageNode::StorageNode(std::unique_ptr<MessageChannelReadHalf> req_half,
                         std::unique_ptr<MessageChannelWriteHalf> rsp_half)
    : NodeThread("storage"), req_half_(std::move(req_half)), rsp_half_(std::move(rsp_half)) {
  // TODO: get a storage service stub from somewhere less hard-coded.
  storage_service_ = oak::Storage::NewStub(
      grpc::CreateChannel("localhost:7867", grpc::InsecureChannelCredentials()));
}

void StorageNode::Run() {
  while (true) {
    ReadResult result = req_half_->BlockingRead(INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }

    StorageChannelRequest channel_request;
    channel_request.ParseFromString(std::string(result.data->data(), result.data->size()));

    // Forward the request to the storage service.
    grpc::Status status;
    grpc::ClientContext context;
    StorageChannelResponse channel_response;
    switch (channel_request.operation_case()) {
      case StorageChannelRequest::kReadRequest: {
        StorageReadRequest read_request;
        read_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        read_request.set_transaction_id(channel_request.read_request().transaction_id());
        read_request.set_datum_name(channel_request.read_request().datum_name());

        StorageReadResponse read_response;
        status = storage_service_->Read(&context, read_request, &read_response);
        if (status.ok()) {
          channel_response.mutable_read_response()->set_datum_value(read_response.datum_value());
        }
        break;
      }
      case StorageChannelRequest::kWriteRequest: {
        StorageWriteRequest write_request;
        write_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        write_request.set_transaction_id(channel_request.write_request().transaction_id());
        write_request.set_datum_name(channel_request.write_request().datum_name());
        write_request.set_datum_value(channel_request.write_request().datum_value());

        StorageWriteResponse write_response;
        status = storage_service_->Write(&context, write_request, &write_response);
        break;
      }
      case StorageChannelRequest::kDeleteRequest: {
        StorageDeleteRequest delete_request;
        delete_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        delete_request.set_transaction_id(channel_request.delete_request().transaction_id());
        delete_request.set_datum_name(channel_request.delete_request().datum_name());

        StorageDeleteResponse delete_response;
        status = storage_service_->Delete(&context, delete_request, &delete_response);
        break;
      }
      case StorageChannelRequest::kBeginRequest: {
        StorageBeginRequest begin_request;
        begin_request.set_storage_id(GetStorageId(channel_request.storage_name()));

        StorageBeginResponse begin_response;
        status = storage_service_->Begin(&context, begin_request, &begin_response);
        if (status.ok()) {
          channel_response.mutable_begin_response()->set_transaction_id(
              begin_response.transaction_id());
        }
        break;
      }
      case StorageChannelRequest::kCommitRequest: {
        StorageCommitRequest commit_request;
        commit_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        commit_request.set_transaction_id(channel_request.commit_request().transaction_id());

        StorageCommitResponse commit_response;
        status = storage_service_->Commit(&context, commit_request, &commit_response);
        break;
      }
      case StorageChannelRequest::kRollbackRequest: {
        StorageRollbackRequest rollback_request;
        rollback_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        rollback_request.set_transaction_id(channel_request.rollback_request().transaction_id());

        StorageRollbackResponse rollback_response;
        status = storage_service_->Rollback(&context, rollback_request, &rollback_response);
        break;
      }
      case StorageChannelRequest::OPERATION_NOT_SET: {
        LOG(ERROR) << "unknown operation";
        status =
            grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Operation request field not set.");
      }
    }
    if (!status.ok()) {
      LOG(ERROR) << "operation failed: " << status.error_code() << " " << status.error_message();
    }
    channel_response.mutable_status()->set_code(status.error_code());
    channel_response.mutable_status()->set_message(status.error_message());

    // Serialize the response and write it back to the Node's STORAGE_IN channel
    std::string rsp_data;
    channel_response.SerializeToString(&rsp_data);
    // TODO: figure out a way to avoid the extra copy (into then out of std::string)
    std::unique_ptr<Message> rsp_msg = absl::make_unique<Message>(rsp_data.begin(), rsp_data.end());
    rsp_half_->Write(std::move(rsp_msg));
  }
}

}  // namespace oak

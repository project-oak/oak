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

#include "storage_channel.h"

namespace oak {

StorageChannel::StorageChannel(std::unique_ptr<Storage::Stub> storage_service)
    : storage_service_(std::move(storage_service)) {}

uint32_t StorageChannel::Write(absl::Span<const char> request_data) {
  grpc::Status status;
  grpc::ClientContext context;
  StorageOperationRequest operation_request;
  StorageOperationResponse operation_response;

  operation_request.ParseFromString(std::string(request_data.data(), request_data.size()));

  switch (operation_request.operation_case()) {
    case StorageOperationRequest::kReadRequest: {
      ReadResponse response;
      status = storage_service_->Read(&context, operation_request.read_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_read_response() = response;
      }
      break;
    }
    case StorageOperationRequest::kWriteRequest: {
      WriteResponse response;
      status = storage_service_->Write(&context, operation_request.write_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_write_response() = response;
      }
      break;
    }
    case StorageOperationRequest::kDeleteRequest: {
      DeleteResponse response;
      status = storage_service_->Delete(&context, operation_request.delete_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_delete_response() = response;
      }
      break;
    }
    case StorageOperationRequest::kBeginRequest: {
      BeginResponse response;
      status = storage_service_->Begin(&context, operation_request.begin_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_begin_response() = response;
      }
      break;
    }
    case StorageOperationRequest::kCommitRequest: {
      CommitResponse response;
      status = storage_service_->Commit(&context, operation_request.commit_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_commit_response() = response;
      }
      break;
    }
    case StorageOperationRequest::kRollbackRequest: {
      RollbackResponse response;
      status =
          storage_service_->Rollback(&context, operation_request.rollback_request(), &response);
      if (status.ok()) {
        *operation_response.mutable_rollback_response() = response;
      }
      break;
    }
    case StorageOperationRequest::OPERATION_NOT_SET: {
      status = grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Operation request field not set.");
    }
  }
  operation_response.mutable_status()->set_code(status.error_code());
  operation_response.mutable_status()->set_message(status.error_message());
  operation_response.SerializeToString(&operation_response_data_);

  return 0;
}

absl::Span<const char> StorageChannel::Read(uint32_t size) {
  return absl::Span<const char>(operation_response_data_.data(), operation_response_data_.size());
}

}  // namespace oak

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

#include "storage_write_channel.h"

namespace oak {

static std::string GetStorageId(const std::string& storage_name) {
  // TODO: Generate name-based UUID.
  return storage_name;
}

StorageWriteChannel::StorageWriteChannel(Storage::Stub* storage_service,
                                         StorageManager* storage_manager)
    : storage_service_(oak::Storage::NewStub(
          grpc::CreateChannel("localhost:7867", grpc::InsecureChannelCredentials()))),
      storage_manager_(storage_manager) {}

uint32_t StorageWriteChannel::Write(absl::Span<const char> request_data) {
  grpc::Status status;
  grpc::ClientContext context;
  StorageOperationRequest operation_request;
  StorageOperationResponse operation_response;

  operation_request.ParseFromString(std::string(request_data.data(), request_data.size()));

  switch (operation_request.operation_case()) {
    case StorageOperationRequest::kReadRequest: {
      operation_request.mutable_read_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Read(&context, operation_request.read_request(),
                                      operation_response.mutable_read_response());
      break;
    }
    case StorageOperationRequest::kWriteRequest: {
      operation_request.mutable_write_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Write(&context, operation_request.write_request(),
                                       operation_response.mutable_write_response());
      break;
    }
    case StorageOperationRequest::kDeleteRequest: {
      operation_request.mutable_delete_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Delete(&context, operation_request.delete_request(),
                                        operation_response.mutable_delete_response());
      break;
    }
    case StorageOperationRequest::kBeginRequest: {
      operation_request.mutable_begin_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Begin(&context, operation_request.begin_request(),
                                       operation_response.mutable_begin_response());
      break;
    }
    case StorageOperationRequest::kCommitRequest: {
      operation_request.mutable_commit_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Commit(&context, operation_request.commit_request(),
                                        operation_response.mutable_commit_response());
      break;
    }
    case StorageOperationRequest::kRollbackRequest: {
      operation_request.mutable_rollback_request()->set_storage_id(
          GetStorageId(operation_request.storage_name()));
      status = storage_service_->Rollback(&context, operation_request.rollback_request(),
                                          operation_response.mutable_rollback_response());
      break;
    }
    case StorageOperationRequest::OPERATION_NOT_SET: {
      status = grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Operation request field not set.");
    }
  }
  operation_response.mutable_status()->set_code(status.error_code());
  operation_response.mutable_status()->set_message(status.error_message());

  std::string response_data;
  operation_response.SerializeToString(&response_data);
  storage_manager_->WriteResponseData(response_data);

  return request_data.size();
}

}  // namespace oak

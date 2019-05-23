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

#include "storage_service.h"

namespace oak {

#include "oak/proto/storage.grpc.pb.h"

using grpc::experimental::ServerCallbackRpcController;

StorageService::StorageService(StorageProvider* storage_provider)
    : storage_provider_(storage_provider) {}

void StorageService::Read(grpc::ServerContext* context, const ReadRequest* request,
                          ReadResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Read(request, response));
}

void StorageService::Write(grpc::ServerContext* context, const WriteRequest* request,
                           WriteResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Write(request, response));
}

void StorageService::Delete(grpc::ServerContext* context, const DeleteRequest* request,
                            DeleteResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Delete(request, response));
}

void StorageService::Begin(grpc::ServerContext* context, const BeginRequest* request,
                           BeginResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Begin(request, response));
}

void StorageService::Commit(grpc::ServerContext* context, const CommitRequest* request,
                            CommitResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Commit(request, response));
}

void StorageService::Rollback(grpc::ServerContext* context, const RollbackRequest* request,
                              RollbackResponse* response, ServerCallbackRpcController* controller) {
  controller->Finish(storage_provider_->Rollback(request, response));
}

}  // namespace oak

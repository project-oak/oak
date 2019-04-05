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

#include "oak/server/grpc_stream.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"

namespace oak {

namespace {

// Converts a gRPC ByteBuffer into a vector of bytes.
std::vector<uint8_t> Unwrap(const ::grpc::ByteBuffer& buffer) {
  std::vector<uint8_t> bytes;
  std::vector<::grpc::Slice> slices;
  ::grpc::Status status = buffer.Dump(&slices);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not unwrap buffer";
  }
  for (const auto& slice : slices) {
    bytes.insert(bytes.end(), slice.begin(), slice.end());
  }
  return bytes;
}

// Converts a vector of bytes into a gRPC ByteBuffer.
const ::grpc::ByteBuffer Wrap(const std::vector<uint8_t>& bytes) {
  ::grpc::Slice slice(bytes.data(), bytes.size());
  ::grpc::ByteBuffer buffer(&slice, /*nslices=*/1);
  return buffer;
}

}  // namespace

void GrpcStream::Start() {
  auto* callback = new std::function<void(bool)>(
      std::bind(&GrpcStream::ReadRequest, this, std::placeholders::_1));
  service_->RequestCall(&context_, &stream_, queue_, queue_, callback);
}

void GrpcStream::ReadRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  auto* callback = new std::function<void(bool)>(
      std::bind(&GrpcStream::ProcessRequest, this, std::placeholders::_1));
  stream_.Read(&request_, callback);
}

void GrpcStream::ProcessRequest(bool ok) {
  if (!ok) {
    delete this;
    return;
  }
  std::vector<uint8_t> request_data = Unwrap(request_);
  std::vector<uint8_t> response_data;
  node_->ProcessModuleCall(&context_, request_data, &response_data);

  // Restarts the gRPC flow with a new GrpcStream object for the next request
  // after processing this request.  This ensures that processing is serialized.
  auto* request = new GrpcStream(service_, queue_, node_);
  request->Start();

  response_ = Wrap(response_data);
  ::grpc::WriteOptions options;
  auto* callback =
      new std::function<void(bool)>(std::bind(&GrpcStream::Finish, this, std::placeholders::_1));
  stream_.WriteAndFinish(response_, options, ::grpc::Status::OK, callback);
}

void GrpcStream::Finish(bool ok) { delete this; }

}  // namespace oak

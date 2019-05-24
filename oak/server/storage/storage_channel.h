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

#ifndef OAK_SERVER_STORAGE_CHANNEL_H_
#define OAK_SERVER_STORAGE_CHANNEL_H_

#include "absl/types/span.h"
#include "oak/proto/storage.grpc.pb.h"
#include "oak/server/channel.h"

namespace oak {

// A channel implementation that reads from and writes to StorageService.
class StorageChannel final : public Channel {
 public:
  // Takes ownership of storage_service.
  explicit StorageChannel(std::unique_ptr<Storage::Stub> storage_service);

  // Takes a serialized StorageOperationRequest protocol message in
  // request_data.  Parses the request and dispatches it to the corresponding
  // StorageService method.  Must be called before Read.
  uint32_t Write(absl::Span<const char> request_data) override;

  // Returns a serialized StorageOperationResponse protocol message containing
  // the response from the StorageService method.  Must be called after Write.
  // The size argument is ignored.
  absl::Span<const char> Read(uint32_t size) override;

 private:
  std::unique_ptr<Storage::Stub> storage_service_;

  std::string operation_response_data_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_CHANNEL_H_

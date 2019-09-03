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

#ifndef OAK_SERVER_STORAGE_WRITE_CHANNEL_H_
#define OAK_SERVER_STORAGE_WRITE_CHANNEL_H_

#include "oak/proto/storage.grpc.pb.h"
#include "oak/server/channel.h"
#include "oak/server/storage/storage_manager.h"

namespace oak {

// A channel implementation that writes to a StorageService.
class StorageWriteChannel final : public ChannelHalf {
 public:
  // Caller retains ownership of storage_manager.
  explicit StorageWriteChannel(StorageManager* storage_manager);

  // Takes a serialized StorageOperationRequest protocol message in
  // request_data.  Parses the request and dispatches it to the corresponding
  // StorageService method.  Must be called before StorageReadChannel::Read.
  void Write(std::unique_ptr<Message>) override;

 private:
  std::unique_ptr<oak::Storage::Stub> storage_service_;
  StorageManager* storage_manager_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_WRITE_CHANNEL_H_

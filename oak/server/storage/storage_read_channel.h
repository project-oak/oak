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

#ifndef OAK_SERVER_STORAGE_READ_CHANNEL_H_
#define OAK_SERVER_STORAGE_READ_CHANNEL_H_

#include "absl/types/span.h"
#include "oak/proto/storage.grpc.pb.h"
#include "oak/server/channel.h"
#include "oak/server/storage/storage_manager.h"

namespace oak {

// A channel implementation that reads from a StorageService.
class StorageReadChannel final : public ChannelHalf {
 public:
  // Caller retains ownership of storage_manager.
  explicit StorageReadChannel(StorageManager* storage_manager);

  // Returns size bytes of the serialized StorageOperationResponse protocol
  // message containing the response from the StorageService method.
  // Must be called repeatedly until an empty result is returned.
  ChannelHalf::Result Read(uint32_t size) override;

 private:
  StorageManager* storage_manager_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_READ_CHANNEL_H_

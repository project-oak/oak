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

#include "storage_read_channel.h"

namespace oak {

StorageReadChannel::StorageReadChannel(StorageManager* storage_manager)
    : storage_manager_(storage_manager) {}

ReadResult StorageReadChannel::Read(uint32_t size) {
  std::unique_ptr<Message> response_data = storage_manager_->ReadResponseData(size);
  ReadResult result{0};
  if (size >= response_data->size()) {
    result.data = std::move(response_data);
  } else {
    result.required_size = response_data->size();
  }
  return result;
}

}  // namespace oak

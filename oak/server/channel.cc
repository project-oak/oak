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

#include "oak/server/channel.h"

#include "asylo/util/logging.h"

namespace oak {

size_t MessageChannel::Count() const {
  absl::ReaderMutexLock lock(&mu_);
  return msgs_.size();
}

void MessageChannel::Write(std::unique_ptr<Message> data) {
  if (data == nullptr) {
    LOG(WARNING) << "Ignoring attempt to write null message";
    return;
  }
  absl::MutexLock lock(&mu_);
  LOG(INFO) << "Add message of size " << data->size();
  msgs_.push_back(std::move(data));
}

ReadResult MessageChannel::Read(uint32_t size) {
  ReadResult result = {0};
  absl::MutexLock lock(&mu_);
  if (msgs_.empty()) {
    return result;
  }
  size_t actual_size = msgs_.front()->size();
  if (actual_size > size) {
    LOG(INFO) << "Next message of size " << actual_size << ", size limited to " << size;
    result.required_size = actual_size;
    return result;
  }
  result.data = std::move(msgs_.front());
  msgs_.pop_front();
  LOG(INFO) << "Read message of size " << result.data->size() << " from channel, size limit "
            << size;
  return std::move(result);
}

}  // namespace oak

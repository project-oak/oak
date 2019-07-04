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

#ifndef OAK_SERVER_BUFFER_CHANNEL_H_
#define OAK_SERVER_BUFFER_CHANNEL_H_

#include "asylo/util/logging.h"
#include "oak/server/channel.h"

namespace oak {

// A channel implementation that only has a receive half, which reads a single
// message from a fixed buffer provided at construction.  The channel does not
// own the provided buffer, so the caller must ensure its lifetime is longer
// than that of the channel.
class ReadMessageChannelHalf final : public ChannelHalf {
 public:
  ReadMessageChannelHalf(absl::Span<const char> data) : data_(data) {}

  ReadResult Read(uint32_t size) override {
    ReadResult result{0};
    if (size >= data_.size()) {
      LOG(INFO) << "Reading all " << data_.size() << " bytes from channel into space of size "
                << size;
      result.data = data_;
      data_.remove_prefix(data_.size());
    } else {
      LOG(INFO) << "Need to read " << data_.size() << " bytes from channel but only " << size
                << " bytes of space available";
      result.required_size = data_.size();
    }
    return result;
  }

 private:
  // This is a view of the data which advances each time the Read method is called.
  absl::Span<const char> data_;
};

// A channel implementation that only has a send half, which writes to an output
// buffer.  The channel does not own the provided buffer, so the caller must ensure
// its lifetime is longer than that of the channel.
class WriteBufferChannelHalf final : public ChannelHalf {
 public:
  WriteBufferChannelHalf(std::vector<char>* data) : data_(data) {
    if (data_ == nullptr) {
      LOG(ERROR) << "Channel has no output buffer, all written data will be discarded";
    }
  }

  uint32_t Write(absl::Span<const char> data) override {
    LOG(INFO) << "Writing to channel: " << data.size() << " bytes";
    if (data_ == nullptr) {
      LOG(WARNING) << "Channel has no output buffer, discarding written data";
      return 0;
    }
    data_->insert(data_->end(), data.cbegin(), data.cend());
    return data.size();
  }

 private:
  // Data is inserted into owner's vector each time the Write method is called.
  std::vector<char>* data_;
};

}  // namespace oak

#endif  // OAK_SERVER_BUFFER_CHANNEL_H_

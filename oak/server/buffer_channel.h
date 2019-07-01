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

// A channel implementation that forwards read and writes to underlying local buffers, keeping track
// of read and write cursors.
//
// The channel owns the output buffer (std::vector), but does not own the input buffer (absl::Span).
class BufferChannel final : public ChannelHalf {
 public:
  BufferChannel(absl::Span<const char> data_input, std::vector<char>* data_output)
      : data_input_(data_input), data_output_(data_output){};

  absl::Span<const char> Read(uint32_t size) override {
    LOG(INFO) << "Reading from channel: " << size << " bytes";
    absl::Span<const char> data = data_input_.subspan(0, size);
    data_input_.remove_prefix(data.size());
    return data;
  };

  uint32_t Write(absl::Span<const char> data) override {
    LOG(INFO) << "Writing to channel: " << data.size() << " bytes";
    if (data_output_ == nullptr) {
      LOG(WARNING) << "Channel is read-only, discarding output";
      return 0;
    }
    data_output_->insert(data_output_->end(), data.cbegin(), data.cend());
    return data.size();
  };

 private:
  // This is a view of the data which advances each time the Read method is called.
  absl::Span<const char> data_input_;

  // Data is inserted each time the Write method is called.
  std::vector<char>* data_output_;
};

}  // namespace oak

#endif  // OAK_SERVER_BUFFER_CHANNEL_H_

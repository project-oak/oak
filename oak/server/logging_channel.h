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

#ifndef OAK_SERVER_LOGGING_CHANNEL_H
#define OAK_SERVER_LOGGING_CHANNEL_H

#include "oak/server/channel.h"

namespace oak {

// A channel implementation that logs to stderr the data written to it.
//
// Reading from this channel always returns an empty Span.
class LoggingChannel final : public Channel {
 public:
  absl::Span<const char> Read(uint32_t size) override {
    absl::Span<const char> empty;
    return empty;
  }

  uint32_t Write(absl::Span<const char> data) override {
    std::string log_message(data.cbegin(), data.cend());
    LOG(INFO) << "LOG: " << log_message;
  };
};

}  // namespace oak

#endif  // OAK_SERVER_LOGGING_CHANNEL_H

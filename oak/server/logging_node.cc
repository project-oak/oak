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

#include "oak/server/logging_node.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"

namespace oak {

void LoggingNode::AddChannel(std::unique_ptr<MessageChannelReadHalf> half) {
  handle_ = OakNode::AddChannel(std::move(half));
}

void LoggingNode::Run() {
  // Borrow pointer to the channel half.
  ChannelHalf* channel = BorrowChannel(handle_);
  if (channel == nullptr) {
    LOG(ERROR) << "No channel available!";
    return;
  }
  std::vector<std::unique_ptr<ChannelStatus>> status;
  status.push_back(absl::make_unique<ChannelStatus>(handle_));
  while (true) {
    if (!WaitOnChannels(&status)) {
      LOG(WARNING) << "Node termination requested";
      return;
    }
    ReadResult result = channel->Read(INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }
    LOG(INFO) << "LOG: " << std::string(result.data->data(), result.data->size());
  }
}

}  // namespace oak

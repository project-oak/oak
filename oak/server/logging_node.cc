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
#include "oak/common/app_config.h"

namespace oak {

void LoggingNode::Run(Handle handle) {
  // Borrow pointer to the channel half.
  handle = FindChannel(kLoggingNodePortName);
  MessageChannelReadHalf* channel = BorrowReadChannel(handle);
  if (channel == nullptr) {
    LOG(ERROR) << "{" << name_ << "} No channel available!";
    return;
  }
  std::vector<std::unique_ptr<ChannelStatus>> status;
  status.push_back(absl::make_unique<ChannelStatus>(handle));
  while (true) {
    if (!WaitOnChannels(&status)) {
      LOG(WARNING) << "{" << name_ << "} Node termination requested, " << channel->Count()
                   << " log messages pending";
      return;
    }
    ReadResult result = channel->Read(INT_MAX, INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "{" << name_ << "} Message size too large: " << result.required_size;
      return;
    }
    LOG(INFO) << "LOG: " << std::string(result.msg->data.data(), result.msg->data.size());
    // Any channel references included with the message will be dropped.
  }
}

}  // namespace oak

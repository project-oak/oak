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
#include "oak/common/logging.h"
#include "oak/proto/log.pb.h"

namespace oak {

void LoggingNode::Run(Handle handle) {
  // Borrow pointer to the channel half.
  MessageChannelReadHalf* channel = BorrowReadChannel(handle);
  if (channel == nullptr) {
    OAK_LOG(ERROR) << "{" << name_ << "} No channel available!";
    return;
  }
  std::vector<std::unique_ptr<ChannelStatus>> status;
  status.push_back(absl::make_unique<ChannelStatus>(handle));
  bool done = false;
  while (!done) {
    if (!WaitOnChannels(&status)) {
      OAK_LOG(WARNING) << "{" << name_ << "} Node termination requested, " << channel->Count()
                       << " log messages pending";
      done = true;
    }
    while (true) {
      ReadResult result = channel->Read(INT_MAX, INT_MAX);
      if (result.status != OakStatus::OK) {
        OAK_LOG(ERROR) << "{" << name_ << "} Failed to read message: " << result.status;
        return;
      }
      if (result.msg == nullptr) {
        break;
      }
      oak::log::LogMessage log_msg;
      bool successful_parse =
          log_msg.ParseFromArray(result.msg->data.data(), result.msg->data.size());
      if (successful_parse) {
        // TODO(#630): when information flow control is implemented, this
        // logging should be governed by that (rather than by the compile-time
        // OAK_DEBUG flag).
        OAK_LOG(INFO) << "{" << name_ << "} "
                      << "LOG: " << oak::log::Level_Name(log_msg.level()) << " " << log_msg.file()
                      << ":" << log_msg.line() << ": " << log_msg.message();
      } else {
        OAK_LOG(ERROR) << "{" << name_ << "} Could not parse LogMessage.";
      }
      // Any channel references included with the message will be dropped.
    }
  }
  if (CloseChannel(handle)) {
    OAK_LOG(INFO) << "{" << name_ << "} Closed channel handle: " << handle;
  } else {
    OAK_LOG(WARNING) << "{" << name_ << "} Invalid channel handle: " << handle;
  }
}

}  // namespace oak

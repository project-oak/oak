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

#include "oak/server/oak_node.h"

#include "asylo/util/logging.h"

namespace oak {

Handle OakNode::AddNamedChannel(const std::string& port_name, std::unique_ptr<ChannelHalf> half) {
  absl::MutexLock lock(&mu_);
  Handle handle = ++next_handle_;
  LOG(INFO) << "port name '" << port_name << "' maps to handle " << handle;
  named_channels_[port_name] = handle;
  channel_halves_[handle] = std::move(half);
  return handle;
}

Handle OakNode::AddChannel(std::unique_ptr<ChannelHalf> half) {
  absl::MutexLock lock(&mu_);
  Handle handle = ++next_handle_;
  channel_halves_[handle] = std::move(half);
  return handle;
}

ChannelHalf* OakNode::BorrowChannel(Handle handle) {
  absl::ReaderMutexLock lock(&mu_);
  return channel_halves_[handle].get();
}

MessageChannelReadHalf* OakNode::BorrowReadChannel(Handle handle) {
  absl::ReaderMutexLock lock(&mu_);
  ChannelHalf* half = channel_halves_[handle].get();
  if (half == nullptr) {
    return nullptr;
  }
  auto value = absl::get_if<std::unique_ptr<MessageChannelReadHalf>>(half);
  if (value == nullptr) {
    return nullptr;
  }
  return value->get();
}

MessageChannelWriteHalf* OakNode::BorrowWriteChannel(Handle handle) {
  absl::ReaderMutexLock lock(&mu_);
  ChannelHalf* half = channel_halves_[handle].get();
  if (half == nullptr) {
    return nullptr;
  }
  auto value = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half);
  if (value == nullptr) {
    return nullptr;
  }
  return value->get();
}

Handle OakNode::FindChannel(const std::string& port_name) {
  absl::ReaderMutexLock lock(&mu_);
  auto it = named_channels_.find(port_name);
  if (it == named_channels_.end()) {
    return 0;
  }
  return it->second;
}

bool OakNode::WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) {
  bool done = false;
  while (!done) {
    for (uint32_t ii = 0; ii < statuses->size(); ii++) {
      uint64_t handle = (*statuses)[ii]->handle;
      MessageChannelReadHalf* channel = BorrowReadChannel(handle);
      if (channel == nullptr) {
        LOG(WARNING) << "Waiting on non-existent read channel handle " << handle;
        continue;
      }
      if (channel->CanRead()) {
        LOG(INFO) << "Message available on handle " << handle;
        done = true;
        (*statuses)[ii]->ready = true;
      }
    }
    if (termination_pending_.load()) {
      LOG(WARNING) << "Node is pending termination";
      return false;
    }
    if (!done) {
      // TODO: get rid of polling wait
      absl::SleepFor(absl::Milliseconds(100));
    }
  }
  return true;
}

}  // namespace oak

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
  LOG(INFO) << "{" << name_ << "} port name '" << port_name << "' maps to handle " << handle;
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

bool OakNode::CloseChannel(Handle handle) {
  absl::MutexLock lock(&mu_);
  auto it = channel_halves_.find(handle);
  if (it == channel_halves_.end()) {
    return false;
  }
  channel_halves_.erase(it);

  // Loop over named channels (under the assumption that there won't be too
  // many) to remove any named reference to this channel handle.
  for (const auto& name_it : named_channels_) {
    if (name_it.second == handle) {
      named_channels_.erase(name_it.first);
      break;
    }
  }
  return true;
}

ChannelHalf* OakNode::BorrowChannel(Handle handle) const {
  absl::ReaderMutexLock lock(&mu_);
  auto it = channel_halves_.find(handle);
  if (it == channel_halves_.end()) {
    return nullptr;
  }
  return it->second.get();
}

MessageChannelReadHalf* OakNode::BorrowReadChannel(Handle handle) const {
  absl::ReaderMutexLock lock(&mu_);
  auto it = channel_halves_.find(handle);
  if (it == channel_halves_.end()) {
    return nullptr;
  }
  ChannelHalf* half = it->second.get();
  auto value = absl::get_if<std::unique_ptr<MessageChannelReadHalf>>(half);
  if (value == nullptr) {
    return nullptr;
  }
  return value->get();
}

MessageChannelWriteHalf* OakNode::BorrowWriteChannel(Handle handle) const {
  absl::ReaderMutexLock lock(&mu_);
  auto it = channel_halves_.find(handle);
  if (it == channel_halves_.end()) {
    return nullptr;
  }
  ChannelHalf* half = it->second.get();
  auto value = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half);
  if (value == nullptr) {
    return nullptr;
  }
  return value->get();
}

Handle OakNode::FindChannel(const std::string& port_name) const {
  absl::ReaderMutexLock lock(&mu_);
  auto it = named_channels_.find(port_name);
  if (it == named_channels_.end()) {
    return 0;
  }
  return it->second;
}

bool OakNode::WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const {
  while (true) {
    bool found_ready = false;
    bool found_readable = false;
    for (uint32_t ii = 0; ii < statuses->size(); ii++) {
      uint64_t handle = (*statuses)[ii]->handle;
      MessageChannelReadHalf* channel = BorrowReadChannel(handle);
      if (channel == nullptr) {
        LOG(WARNING) << "{" << name_ << "} Waiting on non-existent read channel handle " << handle;
        (*statuses)[ii]->status = ChannelReadStatus::INVALID_CHANNEL;
        continue;
      }
      if (channel->CanRead()) {
        LOG(INFO) << "{" << name_ << "} Message available on handle " << handle;
        found_ready = true;
        (*statuses)[ii]->status = ChannelReadStatus::READ_READY;
      } else if (channel->Orphaned()) {
        LOG(INFO) << "{" << name_ << "} Handle " << handle << " is orphaned (no extant writers)";
        (*statuses)[ii]->status = ChannelReadStatus::ORPHANED;
      } else {
        found_readable = true;
        (*statuses)[ii]->status = ChannelReadStatus::NOT_READY;
      }
    }

    if (termination_pending_.load()) {
      LOG(WARNING) << "{" << name_ << "} Node is pending termination";
      return false;
    }
    if (found_ready) {
      return true;
    }
    if (!found_readable) {
      LOG(WARNING) << "{" << name_ << "} No read-capable channels found";
      return false;
    }

    // TODO: get rid of polling wait
    absl::SleepFor(absl::Milliseconds(100));
  }
}

}  // namespace oak

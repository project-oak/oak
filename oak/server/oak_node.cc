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

Handle OakNode::FindChannel(const std::string& port_name) {
  absl::ReaderMutexLock lock(&mu_);
  auto it = named_channels_.find(port_name);
  if (it == named_channels_.end()) {
    return 0;
  }
  return it->second;
}

}  // namespace oak

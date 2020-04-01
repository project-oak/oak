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

#include "absl/memory/memory.h"
#include "oak/common/logging.h"
#include "oak/server/notification.h"

namespace oak {

NodeReadResult OakNode::ChannelRead(Handle handle, uint32_t max_size, uint32_t max_channels) {
  // Borrowing a reference to the channel is safe because the node is single
  // threaded and so cannot invoke channel_close while channel_read is
  // ongoing.
  MessageChannelReadHalf* channel = BorrowReadChannel(handle);
  if (channel == nullptr) {
    OAK_LOG(WARNING) << "{" << name_ << "} Invalid channel handle: " << handle;
    return NodeReadResult(OakStatus::ERR_BAD_HANDLE);
  }
  ReadResult result_internal = channel->Read(max_size, max_channels);
  NodeReadResult result(result_internal.status);
  result.required_size = result_internal.required_size;
  result.required_channels = result_internal.required_channels;
  if (result.status == OakStatus::OK) {
    if (result_internal.msg != nullptr) {
      // Move data and label across into Node-relative message.
      result.msg = absl::make_unique<NodeMessage>();
      result.msg->data = std::move(result_internal.msg->data);
      result.msg->label = std::move(result_internal.msg->label);
      // Transmute channel references to handles in this Node's handle space.
      for (size_t ii = 0; ii < result_internal.msg->channels.size(); ii++) {
        Handle handle = AddChannel(std::move(result_internal.msg->channels[ii]));
        OAK_LOG(INFO) << "{" << name_ << "} Transferred channel has new handle " << handle;
        result.msg->handles.push_back(handle);
      }
    } else {
      // Nothing available to read.
      if (channel->Orphaned()) {
        OAK_LOG(INFO) << "{" << name_ << "} channel_read[" << handle << "]: no writers left";
        result.status = OakStatus::ERR_CHANNEL_CLOSED;
      } else {
        result.status = OakStatus::ERR_CHANNEL_EMPTY;
      }
    }
  }
  return result;
}

OakStatus OakNode::ChannelWrite(Handle handle, std::unique_ptr<NodeMessage> msg) {
  // Borrowing a reference to the channel is safe because the Node is single
  // threaded and so cannot invoke channel_close while channel_write is
  // ongoing.
  MessageChannelWriteHalf* channel = BorrowWriteChannel(handle);
  if (channel == nullptr) {
    OAK_LOG(WARNING) << "{" << name_ << "} Invalid channel handle: " << handle;
    return OakStatus::ERR_BAD_HANDLE;
  }

  if (channel->Orphaned()) {
    OAK_LOG(INFO) << "{" << name_ << "} channel_write[" << handle << "]: no readers left";
    return OakStatus::ERR_CHANNEL_CLOSED;
  }
  auto msg_internal = absl::make_unique<Message>();
  msg_internal->data = std::move(msg->data);
  msg_internal->label = std::move(msg->label);
  for (Handle h : msg->handles) {
    ChannelHalf* half = BorrowChannel(h);
    if (half == nullptr) {
      OAK_LOG(WARNING) << "{" << name_ << "} Invalid transferred channel handle: " << h;
      return OakStatus::ERR_BAD_HANDLE;
    }
    msg_internal->channels.push_back(CloneChannelHalf(half));
  }

  channel->Write(std::move(msg_internal));
  return OakStatus::OK;
}

std::pair<Handle, Handle> OakNode::ChannelCreate() {
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  Handle write_handle = AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.write)));
  Handle read_handle = AddChannel(absl::make_unique<ChannelHalf>(std::move(halves.read)));
  OAK_LOG(INFO) << "{" << name_ << "} Created new channel with handles write=" << write_handle
                << ", read=" << read_handle;
  return std::pair<Handle, Handle>(write_handle, read_handle);
}

OakStatus OakNode::ChannelClose(Handle handle) {
  absl::MutexLock lock(&mu_);
  auto it = channel_halves_.find(handle);
  if (it == channel_halves_.end()) {
    return OakStatus::ERR_BAD_HANDLE;
  }
  channel_halves_.erase(it);
  return OakStatus::OK;
}

OakStatus OakNode::NodeCreate(Handle handle, const std::string& config_name,
                              const std::string& entrypoint_name) {
  // Check that the handle identifies the read half of a channel.
  ChannelHalf* borrowed_half = BorrowChannel(handle);
  if (borrowed_half == nullptr) {
    OAK_LOG(WARNING) << "{" << name_ << "} Invalid channel handle: " << handle;
    return OakStatus::ERR_BAD_HANDLE;
  }
  if (!absl::holds_alternative<std::unique_ptr<MessageChannelReadHalf>>(*borrowed_half)) {
    OAK_LOG(WARNING) << "{" << name_ << "} Wrong direction channel handle: " << handle;
    return OakStatus::ERR_BAD_HANDLE;
  }
  std::unique_ptr<ChannelHalf> half = CloneChannelHalf(borrowed_half);

  OAK_LOG(INFO) << "Create a new node with config '" << config_name << "' and entrypoint '"
                << entrypoint_name << "'";

  std::string node_name;
  if (!runtime_->CreateAndRunNode(config_name, entrypoint_name, std::move(half), &node_name)) {
    return OakStatus::ERR_INVALID_ARGS;
  } else {
    OAK_LOG(INFO) << "Created new node named {" << node_name << "}";
    return OakStatus::OK;
  }
}

Handle OakNode::NextHandle() {
  std::uniform_int_distribution<Handle> distribution;
  while (true) {
    // Keep picking random Handle values until we find an unused (and valid) value.
    Handle handle = distribution(prng_engine_);
    if (handle == kInvalidHandle) {
      continue;
    }
    if (channel_halves_.find(handle) == channel_halves_.end()) {
      return handle;
    }
  }
}

Handle OakNode::AddChannel(std::unique_ptr<ChannelHalf> half) {
  absl::MutexLock lock(&mu_);
  Handle handle = NextHandle();
  channel_halves_[handle] = std::move(half);
  return handle;
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

bool OakNode::WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const {
  while (true) {
    bool found_ready = false;
    bool found_readable = false;
    auto notify = std::make_shared<Notification>();
    for (uint32_t ii = 0; ii < statuses->size(); ii++) {
      uint64_t handle = (*statuses)[ii]->handle;
      MessageChannelReadHalf* channel = BorrowReadChannel(handle);
      if (channel == nullptr) {
        OAK_LOG(WARNING) << "{" << name_ << "} Waiting on non-existent read channel handle "
                         << handle;
        (*statuses)[ii]->status = ChannelReadStatus::INVALID_CHANNEL;
        continue;
      }

      ChannelReadStatus status = channel->ReadStatus(std::weak_ptr<Notification>(notify));
      (*statuses)[ii]->status = status;
      switch (status) {
        case ChannelReadStatus::READ_READY:
          OAK_LOG(INFO) << "{" << name_ << "} Message available on handle " << handle;
          found_ready = true;
          break;
        case ChannelReadStatus::ORPHANED:
          OAK_LOG(INFO) << "{" << name_ << "} Handle " << handle
                        << " is orphaned (no extant writers)";
          break;
        case ChannelReadStatus::NOT_READY:
          found_readable = true;
          break;
        default:
          OAK_LOG(ERROR) << "{" << name_ << "} Unexpected channel read status: " << status;
          return false;
          break;
      }
    }

    if (runtime_->TerminationPending()) {
      OAK_LOG(WARNING) << "{" << name_ << "} Node is pending termination";
      return false;
    }
    if (found_ready) {
      return true;
    }
    if (!found_readable) {
      OAK_LOG(WARNING) << "{" << name_ << "} No read-capable channels found";
      return false;
    }

    // Wait with a timeout to make end-of-day shutdown easier: this means that a
    // node with no pending work will still check termination_pending_
    // occasionally.
    notify->WaitForNotificationWithTimeout(absl::Seconds(1));

    // The only shared_ptr to the Notification object will be dropped here, at
    // which point any still-existing weak_ptr instances will no longer resolve.
  }
}

void OakNode::ClearHandles() {
  absl::MutexLock lock(&mu_);
  OAK_LOG(INFO) << "Dropping " << channel_halves_.size() << " handles for Node";
  channel_halves_.clear();
}

}  // namespace oak

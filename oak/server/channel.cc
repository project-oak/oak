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

#include "oak/server/channel.h"

#include "absl/memory/memory.h"
#include "oak/common/logging.h"

using ::oak_abi::ChannelReadStatus;
using ::oak_abi::OakStatus;

namespace oak {

MessageChannel::ChannelHalves MessageChannel::Create() {
  // (MessageChannel constructor is private so std::make_shared is unavailable)
  std::shared_ptr<MessageChannel> channel(new MessageChannel());
  return ChannelHalves{absl::make_unique<MessageChannelWriteHalf>(channel),
                       absl::make_unique<MessageChannelReadHalf>(channel)};
}

namespace {
ABSL_CONST_INIT absl::Mutex channel_count_mu(absl::kConstInit);
int channel_count;
}  // namespace

MessageChannel::MessageChannel() : reader_count_(0), writer_count_(0) {
  absl::MutexLock lock(&channel_count_mu);
  channel_count++;
  OAK_LOG(INFO) << "Channel created, extant count now " << channel_count;
}

MessageChannel::~MessageChannel() {
  absl::MutexLock lock(&channel_count_mu);
  channel_count--;
  OAK_LOG(INFO) << "Channel destroyed, extant count now " << channel_count;
}

ChannelReadStatus MessageChannel::ReadStatus(std::weak_ptr<Notification> notify) {
  absl::MutexLock lock(&mu_);
  if (msgs_.size() > 0) {
    return ChannelReadStatus::READ_READY;
  } else if (writer_count_ == 0) {
    return ChannelReadStatus::ORPHANED;
  } else {
    notifies_.push_back(notify);
    return ChannelReadStatus::NOT_READY;
  }
}

size_t MessageChannel::Count() const {
  absl::ReaderMutexLock lock(&mu_);
  return msgs_.size();
}

void MessageChannel::Write(std::unique_ptr<Message> msg) {
  if (msg == nullptr) {
    OAK_LOG(WARNING) << "Ignoring attempt to write null message";
    return;
  }
  {
    absl::MutexLock lock(&mu_);
    OAK_LOG(INFO) << "Add message with data size " << msg->data.size() << " and "
                  << msg->channels.size() << " channels";
    msgs_.push_back(std::move(msg));
  }
  TriggerNotifications();
}

ReadResult MessageChannel::Read(uint32_t max_size, uint32_t max_channels) {
  absl::MutexLock lock(&mu_);
  if (msgs_.empty()) {
    ReadResult result(OakStatus::OK);
    return result;
  }
  return ReadLocked(max_size, max_channels);
}

ReadResult MessageChannel::ReadLocked(uint32_t max_size, uint32_t max_channels) {
  Message* next_msg = msgs_.front().get();
  size_t actual_size = next_msg->data.size();
  size_t actual_count = next_msg->channels.size();
  if (actual_size > max_size) {
    OAK_LOG(INFO) << "Next message of size " << actual_size << ", read limited to size "
                  << max_size;
    ReadResult result(OakStatus::ERR_BUFFER_TOO_SMALL);
    result.required_size = actual_size;
    result.required_channels = actual_count;
    return result;
  }
  if (actual_count > max_channels) {
    OAK_LOG(INFO) << "Next message with " << actual_count << " handles, read limited to "
                  << max_channels << " handles";
    ReadResult result(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL);
    result.required_size = actual_size;
    result.required_channels = actual_count;
    return result;
  }
  ReadResult result(OakStatus::OK);
  result.msg = std::move(msgs_.front());
  msgs_.pop_front();
  OAK_LOG(INFO) << "Read message of size " << result.msg->data.size() << " with " << actual_count
                << " channels from channel";
  return result;
}

ReadResult MessageChannel::BlockingRead(uint32_t max_size, uint32_t max_channels) {
  absl::MutexLock lock(&mu_);
  mu_.Await(absl::Condition(
      +[](std::deque<std::unique_ptr<Message>>* msgs) { return msgs->size() > 0; }, &msgs_));
  return ReadLocked(max_size, max_channels);
}

void MessageChannel::Await() {
  absl::MutexLock lock(&mu_);
  mu_.Await(absl::Condition(
      +[](std::deque<std::unique_ptr<Message>>* msgs) { return msgs->size() > 0; }, &msgs_));
}

void MessageChannel::TriggerNotifications() {
  // Trigger any notifications waiting on this channel, but not while holding
  // the lock.
  std::vector<std::weak_ptr<Notification>> notifies;
  {
    absl::MutexLock lock(&mu_);
    std::swap(notifies, notifies_);
  }

  for (auto& possible_notify : notifies) {
    std::shared_ptr<Notification> notify = possible_notify.lock();
    if (notify != nullptr) {
      notify->Notify();
    }
  }
}

namespace {
// At namespace scope because local classes may not have member templates.
struct CloneVariant {
  template <typename T>
  std::unique_ptr<ChannelHalf> operator()(const T& h) const {
    return absl::make_unique<ChannelHalf>(h->Clone());
  }
};
}  // namespace

std::unique_ptr<ChannelHalf> CloneChannelHalf(ChannelHalf* half) {
  CloneVariant visitor;
  return absl::visit(visitor, *half);
}

}  // namespace oak

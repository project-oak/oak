/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/server/notification.h"

#include <thread>
#include <vector>

#include "gtest/gtest.h"
#include "oak/common/logging.h"
#include "oak/server/channel.h"

namespace oak {

TEST(Notification, MultipleNotify) {
  const int kChannelCount = 5;
  const int kWaiterCount = 4;

  std::vector<MessageChannel::ChannelHalves> channels;
  for (int chan = 0; chan < kChannelCount; chan++) {
    channels.push_back(MessageChannel::Create());
  }

  absl::Mutex mu;
  int waiting_count = 0;

  std::vector<std::thread> waiters;
  for (int wait = 0; wait < kWaiterCount; wait++) {
    OAK_LOG(INFO) << "start new waiter thread " << wait;
    waiters.push_back(std::thread([wait, &channels, &mu, &waiting_count] {
      OAK_LOG(INFO) << "new waiter thread " << wait;
      auto notify = std::make_shared<Notification>();
      for (int chan = 0; chan < kChannelCount; chan++) {
        OAK_LOG(INFO) << "register notification for waiter " << wait << " with channel " << chan;
        channels[chan].read->ReadStatus(std::weak_ptr<Notification>(notify));
      }

      mu.Lock();
      waiting_count++;
      mu.Unlock();

      OAK_LOG(INFO) << "waiter thread " << wait << " awaiting...";
      notify->WaitForNotification();
      OAK_LOG(INFO) << "waiter thread " << wait << " awaiting...done";
    }));
  }

  // Make sure all waiters are up and running before writing notifications.
  mu.Lock();
  auto all_up = [&waiting_count] { return waiting_count == kWaiterCount; };
  mu.Await(absl::Condition(&all_up));
  mu.Unlock();

  for (int chan = 0; chan < kChannelCount; chan++) {
    auto msg = absl::make_unique<Message>();
    channels[chan].write->Write(std::move(msg));
  }

  for (int wait = 0; wait < kWaiterCount; wait++) {
    OAK_LOG(INFO) << "await completion of waiter thread " << wait;
    waiters[wait].join();
    OAK_LOG(INFO) << "await completion of waiter thread " << wait << " done";
  }
}

}  // namespace oak

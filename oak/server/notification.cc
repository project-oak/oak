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

namespace oak {

Notification::~Notification() { absl::MutexLock lock(&mu_); }

void Notification::Notify() {
  absl::MutexLock lock(&mu_);
  count_++;
}

void Notification::WaitForNotification() {
  auto notified = [this] { return count_ > 0; };
  absl::MutexLock lock(&mu_);
  mu_.Await(absl::Condition(&notified));
}

bool Notification::WaitForNotificationWithTimeout(absl::Duration timeout) const {
  auto notified = [this] { return count_ > 0; };
  absl::MutexLock lock(&mu_);
  return mu_.AwaitWithTimeout(absl::Condition(&notified), timeout);
}

}  // namespace oak

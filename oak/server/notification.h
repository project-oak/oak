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

#ifndef OAK_SERVER_NOTIFICATION_H_
#define OAK_SERVER_NOTIFICATION_H_

#include "absl/synchronization/mutex.h"
#include "absl/time/time.h"

namespace oak {

// A Notification allows threads to receive notification of an event.
class Notification {
 public:
  Notification() : count_(0) {}
  Notification(const Notification&) = delete;
  Notification& operator=(const Notification&) = delete;
  ~Notification();

  // Trigger the notification.  May be called multiple times.
  void Notify();

  // Await one or more triggers of the notification.
  void WaitForNotification();
  bool WaitForNotificationWithTimeout(absl::Duration timeout) const;

 private:
  mutable absl::Mutex mu_;
  int count_;
};

}  // namespace oak

#endif  // OAK_SERVER_NOTIFICATION_H_

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

#ifndef OAK_SERVER_LOGGING_NODE_H_
#define OAK_SERVER_LOGGING_NODE_H_

#include <memory>
#include <thread>

#include "oak/server/channel.h"

namespace oak {

// TODO: Move common pseudo-node behaviour into base class.

// Pseudo-node to perform logging.
class LoggingNode {
 public:
  LoggingNode(std::unique_ptr<MessageChannelReadHalf> half) : half_(std::move(half)) {}
  ~LoggingNode();

  void Start();
  void Stop();

 private:
  void Run();

  std::unique_ptr<MessageChannelReadHalf> half_;

  std::thread main_;
};

}  // namespace oak

#endif  // OAK_SERVER_LOGGING_NODE_H_

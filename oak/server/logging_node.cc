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

#include "asylo/util/logging.h"

namespace oak {

LoggingNode::~LoggingNode() { Stop(); }

void LoggingNode::Start() {
  LOG(INFO) << "Executing logging pseudo-node on new thread";
  std::thread t([this] { this->Run(); });
  main_ = std::move(t);
  LOG(INFO) << "Started logging execution thread";
}

void LoggingNode::Stop() {
  // TODO: Terminate logging thread somehow, then join() rather than detach()
  main_.detach();
}

void LoggingNode::Run() {
  while (true) {
    ReadResult result = half_->BlockingRead(INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }
    LOG(INFO) << "LOG: " << std::string(result.data->data(), result.data->size());
  }
}

}  // namespace oak

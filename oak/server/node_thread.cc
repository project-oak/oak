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

#include "oak/server/node_thread.h"

#include "asylo/util/logging.h"

namespace oak {

NodeThread::~NodeThread() { Stop(); }

void NodeThread::Start() {
  if (thread_.joinable()) {
    LOG(ERROR) << "Attempt to Start() an already-running NodeThread";
    return;
  }

  LOG(INFO) << "Executing new " << name_ << " node thread";
  thread_ = std::thread(&oak::NodeThread::Run, this);
  LOG(INFO) << "Started " << name_ << " node thread";
}

void NodeThread::Stop() {
  // TODO: Terminate pseudo thread somehow, then join() rather than detach()
  LOG(INFO) << "Abandoning " << name_ << " node thread";
  thread_.detach();
}

}  // namespace oak

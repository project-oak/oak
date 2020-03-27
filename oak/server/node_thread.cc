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

#include "oak/common/logging.h"

namespace oak {

NodeThread::~NodeThread() { StopThread(); }

void NodeThread::Start(Handle handle) {
  if (thread_.joinable()) {
    OAK_LOG(ERROR) << "Attempt to Start() an already-running NodeThread";
    return;
  }
  if (TerminationPending()) {
    OAK_LOG(ERROR) << "Attempt to Start() an already-terminated NodeThread";
    return;
  }

  OAK_LOG(INFO) << "Executing new {" << name_ << "} node thread with handle " << handle;
  thread_ = std::thread(&oak::NodeThread::RunAndCleanup, this, handle);
  OAK_LOG(INFO) << "Started {" << name_ << "} node thread";
}

void NodeThread::Stop() {
  OAK_LOG(INFO) << "Stopping node {" << name_ << "}";
  StopThread();
}

void NodeThread::StopThread() {
  OAK_LOG(INFO) << "Termination pending for {" << name_ << "}";
  if (thread_.joinable()) {
    OAK_LOG(INFO) << "Waiting for completion of {" << name_ << "} node thread";
    thread_.join();
    OAK_LOG(INFO) << "Completed {" << name_ << "} node thread";
  }
}

void NodeThread::RunAndCleanup(Handle handle) {
  Run(handle);
  OAK_LOG(INFO) << "Node's Run() method completed, clear handle table";
  ClearHandles();
}

}  // namespace oak

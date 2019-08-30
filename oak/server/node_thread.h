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

#ifndef OAK_SERVER_NODE_THREAD_H_
#define OAK_SERVER_NODE_THREAD_H_

#include <memory>
#include <thread>

namespace oak {

// This class represents a node or pseudo-node that executes as a distinct
// thread.
class NodeThread {
 public:
  // Construct a thread, identified by the given name in diagnostic messages.
  NodeThread(const std::string& name) : name_(name) {}
  virtual ~NodeThread();

  // Start kicks off a separate thread that invokes the Run() method.
  void Start();

  // Stop terminates the thread associated with the pseudo-node.
  void Stop();

 protected:
  virtual void Run() = 0;

  const std::string name_;

 private:
  std::thread thread_;
};

}  // namespace oak

#endif  // OAK_SERVER_NODE_THREAD_H_

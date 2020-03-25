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

#ifndef OAK_SERVER_HANDLE_CLOSER_H_
#define OAK_SERVER_HANDLE_CLOSER_H_

#include "oak/server/oak_node.h"

namespace oak {

// RAII class to hold a Node's handle and auto-close it on object destruction.
class HandleCloser {
 public:
  explicit HandleCloser(OakNode* node, Handle handle) : node_(node), handle_(handle) {}

  ~HandleCloser() { node_->ChannelClose(handle_); }

  Handle get() const { return handle_; }

 private:
  OakNode* node_;
  const Handle handle_;
};

}  // namespace oak

#endif  // OAK_SERVER_HANDLE_CLOSER_H_

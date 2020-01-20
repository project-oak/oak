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

#ifndef OAK_SERVER_BASE_RUNTIME_H_
#define OAK_SERVER_BASE_RUNTIME_H_

#include <memory>
#include <string>

#include "oak/server/channel.h"

namespace oak {

// BaseRuntime is a abstract base class that describes Oak Runtime functionality
// that is available for Oak Nodes to use; it effectively allows an OakNode
// object to hold a reference to the OakRuntime that owns it, without requiring
// a dependency cycle.
class BaseRuntime {
 public:
  virtual ~BaseRuntime() {}
  virtual bool CreateAndRunNode(const std::string& config, const std::string& entrypoint,
                                std::unique_ptr<ChannelHalf> half, std::string* config_name) = 0;
  virtual bool TerminationPending() = 0;
};  // class BaseRuntime

}  // namespace oak

#endif  // OAK_SERVER_BASE_RUNTIME_H_

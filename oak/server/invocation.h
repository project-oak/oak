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

#ifndef OAK_SERVER_INVOCATION_H_
#define OAK_SERVER_INVOCATION_H_

#include <memory>
#include <string>

#include "oak/common/handles.h"
#include "oak/server/handle_closer.h"
#include "oak/server/oak_node.h"

namespace oak {

// An Invocation holds the channel handles used in gRPC method invocation
// processing.
struct Invocation {
  // Build an Invocation from the data arriving on the given channel.
  static std::unique_ptr<Invocation> ReceiveFromChannel(OakNode* node, Handle invocation_handle);

  Invocation(OakNode* node, Handle req, Handle rsp)
      : req_handle(node, req), rsp_handle(node, rsp) {}

  HandleCloser req_handle;
  HandleCloser rsp_handle;
};

}  // namespace oak

#endif  // OAK_SERVER_GRPC_CLIENT_NODE_H_

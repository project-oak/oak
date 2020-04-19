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

#ifndef OAK_SERVER_ROUGHTIME_CLIENT_NODE_H_
#define OAK_SERVER_ROUGHTIME_CLIENT_NODE_H_

#include <memory>
#include <string>

#include "oak/common/handles.h"
#include "oak/proto/application.pb.h"
#include "oak/server/oak_node.h"
#include "oak/server/time/roughtime_client.h"

namespace oak {

class RoughtimeClientNode final : public OakNode {
 public:
  RoughtimeClientNode(const std::string& name, NodeId node_id,
                      const application::RoughtimeClientConfiguration& config);

 private:
  void Run(Handle handle) override;

  std::unique_ptr<RoughtimeClient> client_;
};

}  // namespace oak

#endif  // OAK_SERVER_GRPC_CLIENT_NODE_H_

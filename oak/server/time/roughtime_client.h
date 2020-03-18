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

#ifndef OAK_SERVER_TIME_ROUGHTIME_CLIENT_H_
#define OAK_SERVER_TIME_ROUGHTIME_CLIENT_H_

#include "protocol.h"
#include "third_party/asylo/statusor.h"

namespace oak {

// Client for getting roughtime (in microseconds since Unix epoch) from multiple servers.
// The list of servers are currently hardcoded in roughttime_client.cc
// Based on https://roughtime.googlesource.com/roughtime/+/refs/heads/master/simple_client.cc
// and https://roughtime.googlesource.com/roughtime/+/refs/heads/master/go/client/client.go
class RoughtimeClient {
 public:
  static oak::StatusOr<roughtime::rough_time_t> GetRoughTime();
};

}  // namespace oak

#endif  // OAK_SERVER_TIME_ROUGHTIME_CLIENT_H_

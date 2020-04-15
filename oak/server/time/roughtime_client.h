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

#include <cstdint>

#include "oak/server/time/roughtime_util.h"
#include "protocol.h"
#include "third_party/asylo/statusor.h"

namespace oak {

// Information to identify a particular Roughtime server.
// Assume we will only support Ed25519 public key and UDP for now.
struct RoughtimeServerSpec {
  std::string name;
  std::string host;
  uint32_t port;
  std::string public_key_base64;
};

namespace roughtime {

// Default Roughtime servers and connection parameters.
extern const std::vector<RoughtimeServerSpec> kDefaultServers;

// The default minimum number of overlapping intervals we need to trust the time.
// If fewer servers than this are configured, the server count will be used
// instead.
extern const int kDefaultMinOverlappingIntervals;

// Default number of seconds that we will wait for a reply from each server.
extern const int kDefaultTimeoutSeconds;

// Default number of times we will retry connecting to each server.
extern const int kDefaultServerRetries;

// Default maximum radius accepted for a Roughtime response (1 minute in microseconds).
extern const uint32_t kDefaultMaxRadiusMicroseconds;

}  // namespace roughtime

// Client for getting Roughtime (in microseconds since Unix epoch) from multiple servers.
// The list of servers are currently hardcoded in roughttime_client.cc
// Based on https://roughtime.googlesource.com/roughtime/+/refs/heads/master/simple_client.cc
// and https://roughtime.googlesource.com/roughtime/+/refs/heads/master/go/client/client.go
class RoughtimeClient {
 public:
  // Construct a Roughtime client that uses the default servers and parameters.
  RoughtimeClient() : RoughtimeClient({}, 0, 0, 0, 0) {}

  // Construct a Roughtime client with the provided servers and parameters.  If
  // any are empty/zero then the default value will be used.
  RoughtimeClient(const std::vector<RoughtimeServerSpec>& servers, int min_overlapping_intervals,
                  int timeout_seconds, int server_retries, uint32_t max_radius_microseconds);

  oak::StatusOr<::roughtime::rough_time_t> GetRoughTime();

 private:
  oak::StatusOr<RoughtimeInterval> GetIntervalFromServer(const RoughtimeServerSpec& server);
  std::vector<RoughtimeServerSpec> servers_;
  int min_overlapping_intervals_;
  int timeout_seconds_;
  int server_retries_;
  uint32_t max_radius_microseconds_;
};

}  // namespace oak

#endif  // OAK_SERVER_TIME_ROUGHTIME_CLIENT_H_

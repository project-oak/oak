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

#include "roughtime_client.h"

#include <arpa/inet.h>
#include <errno.h>
#include <inttypes.h>
#include <netdb.h>
#include <netinet/udp.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_format.h"
#include "client.h"
#include "glog/logging.h"
#include "oak/common/nonce_generator.h"
#include "oak/server/time/roughtime_util.h"
#include "third_party/asylo/status_macros.h"

using ::absl::Status;
using ::oak::StatusOr;

namespace oak {

namespace roughtime {

// Based on
// https://github.com/cloudflare/roughtime/blob/569dc6f5119970035fe0a008b83398d59363ed45/ecosystem.json
const std::vector<RoughtimeServerSpec> kDefaultServers{
    {"Caesium", "caesium.tannerryan.ca", 2002, "iBVjxg/1j7y1+kQUTBYdTabxCppesU/07D4PMDJk2WA="},
    {"Chainpoint", "roughtime.chainpoint.org", 2002,
     "bbT+RPS7zKX6w71ssPibzmwWqU9ffRV5oj2OresSmhE="},
    {"Google", "roughtime.sandbox.google.com", 2002,
     "etPaaIxcBMY1oUeGpwvPMCJMwlRVNxv51KK/tktoJTQ="},
    {"Cloudflare", "roughtime.cloudflare.com", 2002,
     "gD63hSj3ScS+wuOeGrubXlq35N1c5Lby/S+T7MNTjxo="},
    {"mixmin", "ticktock.mixmin.net", 5333, "cj8GsiNlRkqiDElAeNMSBBMwrAl15hYPgX50+GWX/lA="}};

const int kDefaultMinOverlappingIntervals = 3;
const int kDefaultTimeoutSeconds = 3;
const int kDefaultServerRetries = 3;
const uint32_t kDefaultMaxRadiusMicroseconds = 60000000;

}  // namespace roughtime

namespace {

// The size of the receive buffer.
// This seems to be the same as the minimum request size according to the Roughtime samples.
// eg. https://roughtime.googlesource.com/roughtime/+/refs/heads/master/simple_client.cc#250
constexpr size_t kReceiveBufferSize = ::roughtime::kMinRequestSize;

// Creates a UDP socket connected to the host and port.
StatusOr<int> CreateSocket(const std::string& host, uint32_t port) {
  addrinfo hints = {};
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_DGRAM;
  hints.ai_protocol = IPPROTO_UDP;
  hints.ai_flags = AI_NUMERICSERV;
  std::string port_str = absl::StrCat(port);
  addrinfo* address;
  int error = getaddrinfo(host.c_str(), port_str.c_str(), &hints, &address);
  if (error != 0) {
    return Status(absl::StatusCode::kInvalidArgument,
                  absl::StrFormat("Could not resolve %s: %s", host.c_str(), gai_strerror(error)));
  }
  int handle = socket(address->ai_family, address->ai_socktype, address->ai_protocol);
  if (handle < 0) {
    freeaddrinfo(address);
    return Status(absl::StatusCode::kInternal, "Failed to create UDP socket.");
  }
  if (connect(handle, address->ai_addr, address->ai_addrlen)) {
    freeaddrinfo(address);
    close(handle);
    return Status(absl::StatusCode::kInternal, "Failed to open UDP socket.");
  }
  freeaddrinfo(address);
  return handle;
}

StatusOr<std::string> SendRequest(const RoughtimeServerSpec& server,
                                  const Nonce<::roughtime::kNonceLength>& nonce, int server_retries,
                                  int timeout_seconds) {
  StatusOr<int> create_socket_result;
  int attempts = 0;
  do {
    ++attempts;
    create_socket_result = CreateSocket(server.host, server.port);
  } while (!create_socket_result.ok() && attempts <= server_retries);

  if (!create_socket_result.ok()) {
    return Status(absl::StatusCode::kInternal,
                  "Exceeded maximum retries while attempting to connect to " + server.name);
  }

  auto handle = create_socket_result.ValueOrDie();
  timeval timeout = {};
  timeout.tv_sec = timeout_seconds;
  timeout.tv_usec = 0;
  setsockopt(handle, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout));

  const std::string request = ::roughtime::CreateRequest(nonce.data());
  ssize_t send_size;
  do {
    send_size = send(handle, request.data(), request.size(), 0 /* flags */);
  } while (send_size == -1 && errno == EINTR);
  if (send_size != static_cast<ssize_t>(request.size())) {
    close(handle);
    return Status(absl::StatusCode::kInternal,
                  "Network error on sending request to " + server.name);
  }

  char receive_buffer[kReceiveBufferSize];
  ssize_t receive_size;
  do {
    receive_size = recv(handle, receive_buffer, kReceiveBufferSize, 0 /* flags */);
  } while (receive_size == -1 && errno == EINTR);
  close(handle);
  if (receive_size == -1) {
    if (errno == EINTR) {
      return Status(absl::StatusCode::kInternal, "Request timed out for " + server.name);
    }
    return Status(absl::StatusCode::kInternal, "No response received from " + server.name);
  }

  return std::string(receive_buffer, static_cast<size_t>(receive_size));
}

}  // namespace

StatusOr<RoughtimeInterval> RoughtimeClient::GetIntervalFromServer(
    const RoughtimeServerSpec& server) {
  std::string public_key;
  if (!absl::Base64Unescape(server.public_key_base64, &public_key)) {
    return Status(absl::StatusCode::kInvalidArgument,
                  absl::StrFormat("Public key for server %s is not a valid base64 encoding.",
                                  server.name.c_str()));
  }

  oak::NonceGenerator<::roughtime::kNonceLength> generator;
  Nonce<::roughtime::kNonceLength> nonce = generator.NextNonce();
  std::string response;
  OAK_ASSIGN_OR_RETURN(response, SendRequest(server, nonce, server_retries_, timeout_seconds_));

  ::roughtime::rough_time_t timestamp_microseconds;
  uint32_t radius_microseconds;
  std::string error;
  if (!::roughtime::ParseResponse(&timestamp_microseconds, &radius_microseconds, &error,
                                  reinterpret_cast<const uint8_t*>(public_key.data()),
                                  reinterpret_cast<const uint8_t*>(response.data()),
                                  response.size(), nonce.data())) {
    return Status(absl::StatusCode::kInternal,
                  absl::StrFormat("Response from %s could not be parsed: %s", server.name.c_str(),
                                  error.c_str()));
  }

  if (radius_microseconds > max_radius_microseconds_) {
    return Status(absl::StatusCode::kInternal,
                  absl::StrFormat("Radius from %s is too large: %" PRIu32 "", server.name.c_str(),
                                  radius_microseconds));
  }

  if (radius_microseconds > timestamp_microseconds) {
    return Status(absl::StatusCode::kInternal,
                  absl::StrFormat("Timestamp from %s is too small: %" PRIu64 "",
                                  server.name.c_str(), timestamp_microseconds));
  }

  LOG(INFO) << "Time from " << server.name << ": " << timestamp_microseconds << " +/- "
            << radius_microseconds;
  return RoughtimeInterval{(timestamp_microseconds - radius_microseconds),
                           (timestamp_microseconds + radius_microseconds)};
}

RoughtimeClient::RoughtimeClient(const std::vector<RoughtimeServerSpec>& servers,
                                 int min_overlapping_intervals, int timeout_seconds,
                                 int server_retries, uint32_t max_radius_microseconds)
    : servers_(servers.size() > 0 ? servers : roughtime::kDefaultServers),
      min_overlapping_intervals_(min_overlapping_intervals > 0
                                     ? min_overlapping_intervals
                                     : std::min(roughtime::kDefaultMinOverlappingIntervals,
                                                static_cast<int>(servers_.size()))),
      timeout_seconds_(timeout_seconds > 0 ? timeout_seconds : roughtime::kDefaultTimeoutSeconds),
      server_retries_(server_retries > 0 ? server_retries : roughtime::kDefaultServerRetries),
      max_radius_microseconds_(max_radius_microseconds > 0
                                   ? max_radius_microseconds
                                   : roughtime::kDefaultMaxRadiusMicroseconds) {
  if (static_cast<size_t>(min_overlapping_intervals_) > servers_.size()) {
    LOG(ERROR) << "Misconfigured client: requires " << min_overlapping_intervals_
               << " overlapping intervals but only " << servers_.size()
               << " servers configured; all requests will fail!";
  }
}

StatusOr<::roughtime::rough_time_t> RoughtimeClient::GetRoughTime() {
  std::vector<RoughtimeInterval> valid_intervals;
  for (const auto& server : servers_) {
    auto interval_or_status = GetIntervalFromServer(server);
    if (interval_or_status.ok()) {
      valid_intervals.push_back(interval_or_status.ValueOrDie());
    } else {
      LOG(WARNING) << "Could not get status from " << server.name << ":"
                   << interval_or_status.status();
    }
  }

  RoughtimeInterval interval;
  OAK_ASSIGN_OR_RETURN(interval, FindOverlap(valid_intervals, min_overlapping_intervals_));
  return (interval.min + interval.max) / 2;
}

}  // namespace oak

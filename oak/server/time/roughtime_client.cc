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

#include <array>
#include <string>
#include <vector>
//#include <unistd.h>

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_format.h"
#include "asylo/util/logging.h"
#include "asylo/util/status.h"
#include "asylo/util/status_macros.h"
#include "client.h"
#include "oak/common/nonce_generator.h"

using ::asylo::Status;
using ::asylo::StatusOr;

namespace oak {

// Information we need about roughtime servers.
// Assume we will only support Ed25519 public key and UDP for now.
struct RoughtimeServerSpec {
  std::string name;
  std::string host;
  std::string port;
  std::string public_key_base64;
};

struct RoughtimeInterval {
  roughtime::rough_time_t min;
  roughtime::rough_time_t max;
};

const std::vector<RoughtimeServerSpec> servers{{"Google", "roughtime.sandbox.google.com", "2002",
                                                "etPaaIxcBMY1oUeGpwvPMCJMwlRVNxv51KK/tktoJTQ="},
                                               {"Cloudflare", "roughtime.cloudflare.com", "2002",
                                                "gD63hSj3ScS+wuOeGrubXlq35N1c5Lby/S+T7MNTjxo="}};

// TODO: Make multiple requests and calculate overlapping interval.
// The minimum number of overlapping intervals we need to trust the time.
// constexpr int kMinOverlappingTimeIntervals = 2;

// Number of seconds that we will wait for a reply from the server.
constexpr int kTimeoutSeconds = 3;

// TODO: Retry on connection failure.
// Number of times we will retry connecting to the server.
// constexpr int kServerRetries = 3;

// The size of the receive buffer.
// This seems to be the same as the minimum request size according to the Roughtime samples.
// eg. https://roughtime.googlesource.com/roughtime/+/refs/heads/master/simple_client.cc#250
constexpr size_t kReceiveBufferSize = roughtime::kMinRequestSize;

// Maximum radius accepted for a roughtime response.
constexpr uint32_t kMaxRadius = 60000000;

// Creates a UDP socket connected to the host and port.
StatusOr<int> CreateSocket(const std::string& host, const std::string& port) {
  addrinfo hints = {};
  hints.ai_socktype = SOCK_DGRAM;
  hints.ai_protocol = IPPROTO_UDP;
  hints.ai_flags = AI_NUMERICSERV;
  addrinfo* address;
  int error = getaddrinfo(host.c_str(), port.c_str(), &hints, &address);
  if (error != 0) {
    return Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                  absl::StrFormat("Could not resolve %s: %s", host.c_str(), gai_strerror(error)));
  }
  int handle = socket(address->ai_family, address->ai_socktype, address->ai_protocol);
  if (handle < 0) {
    freeaddrinfo(address);
    return Status(asylo::error::GoogleError::INTERNAL, "Failed to create UDP socket.");
  }
  if (connect(handle, address->ai_addr, address->ai_addrlen)) {
    freeaddrinfo(address);
    close(handle);
    return Status(asylo::error::GoogleError::INTERNAL, "Failed to open UDP socket.");
  }
  freeaddrinfo(address);
  return handle;
}

StatusOr<std::string> SendRequest(const RoughtimeServerSpec& server,
                                  const Nonce<roughtime::kNonceLength>& nonce) {
  int handle;
  ASYLO_ASSIGN_OR_RETURN(handle, CreateSocket(server.host, server.port));
  const std::string request = roughtime::CreateRequest(nonce.data());

  timeval timeout = {};
  timeout.tv_sec = kTimeoutSeconds;
  timeout.tv_usec = 0;
  setsockopt(handle, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout));
  ssize_t send_size;
  do {
    send_size = send(handle, request.data(), request.size(), 0 /* flags */);
  } while (send_size == -1 && errno == EINTR);
  if (send_size < 0 || static_cast<size_t>(send_size) != request.size()) {
    close(handle);
    return Status(asylo::error::GoogleError::INTERNAL,
                  "Network error on sending request to " + server.name);
  }

  uint8_t receive_buffer[kReceiveBufferSize];
  ssize_t receive_size;
  do {
    receive_size = recv(handle, receive_buffer, kReceiveBufferSize, 0 /* flags */);
  } while (receive_size == -1 && errno == EINTR);
  close(handle);
  if (receive_size == -1) {
    if (errno == EINTR) {
      return Status(asylo::error::GoogleError::INTERNAL, "Request timed out for " + server.name);
    }
    return Status(asylo::error::GoogleError::INTERNAL, "No response received from " + server.name);
  }

  return std::string(reinterpret_cast<const char*>(receive_buffer),
                     static_cast<size_t>(receive_size));
}

StatusOr<RoughtimeInterval> GetIntervalFromServer(const RoughtimeServerSpec& server) {
  oak::NonceGenerator<roughtime::kNonceLength> generator;
  std::string response;
  Nonce<roughtime::kNonceLength> nonce = generator.NextNonce();
  ASYLO_ASSIGN_OR_RETURN(response, SendRequest(server, nonce));
  roughtime::rough_time_t timestamp;
  uint32_t radius;
  std::string error;
  std::string public_key;
  if (!absl::Base64Unescape(server.public_key_base64, &public_key)) {
    return Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                  absl::StrFormat("Public key for server %s is not a valid base64 encoding.",
                                  server.name.c_str()));
  }

  if (!roughtime::ParseResponse(
          &timestamp, &radius, &error, reinterpret_cast<const uint8_t*>(public_key.data()),
          reinterpret_cast<const uint8_t*>(response.data()), response.size(), nonce.data())) {
    return Status(asylo::error::GoogleError::INTERNAL,
                  absl::StrFormat("Response from %s failed verification: %s", server.name.c_str(),
                                  error.c_str()));
  }

  if (radius > kMaxRadius) {
    return Status(
        asylo::error::GoogleError::INTERNAL,
        absl::StrFormat("Radius from %s is too large: %" PRIu32 "", server.name.c_str(), radius));
  }

  if (radius > timestamp) {
    return Status(asylo::error::GoogleError::INTERNAL,
                  absl::StrFormat("Timestamp from %s is too small: %" PRIu64 "",
                                  server.name.c_str(), timestamp));
  }

  return RoughtimeInterval{(timestamp - radius), (timestamp + radius)};
}

StatusOr<roughtime::rough_time_t> RoughtimeClient::GetRoughTime() {
  // TODO: Connect to all servers and find overlapping intervals.
  // TODO: Implement retries.
  RoughtimeInterval interval;
  ASYLO_ASSIGN_OR_RETURN(interval, GetIntervalFromServer(servers[0]));
  return (interval.min + interval.max) / 2;
}

}  // namespace oak

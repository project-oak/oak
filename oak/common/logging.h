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

#ifndef OAK_COMMON_LOGGING_H_
#define OAK_COMMON_LOGGING_H_

// Define Oak-specific wrapper macros for logging.

#ifdef OAK_DEBUG

// Forward on to gLog.
#include "glog/logging.h"
#define OAK_LOG(severity) COMPACT_GOOGLE_LOG_##severity.stream()

#else

// Definition for compiled-out logging.
#include <ostream>
namespace oak {

/// Class representing a log message that drops all info.
class NullMessage {
 public:
  NullMessage& stream() { return *this; }
};

template <typename T>
inline NullMessage& operator<<(NullMessage& msg, const T&) {
  return msg;
}
inline NullMessage& operator<<(NullMessage& msg, std::ostream& (*)(std::ostream& os)) {
  return msg;
}

}  // namespace oak

#define OAK_LOG(severity) ::oak::NullMessage().stream()

#endif

#endif  // OAK_COMMON_LOGGING_H_

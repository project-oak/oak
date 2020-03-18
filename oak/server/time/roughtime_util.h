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

#ifndef OAK_SERVER_TIME_ROUGHTIME_UTIL_H_
#define OAK_SERVER_TIME_ROUGHTIME_UTIL_H_

#include <vector>

#include "protocol.h"
#include "third_party/asylo/statusor.h"

namespace oak {

// Represents a roughtime interval as the minimum and maximum number of microseconds relative to the
// Unix epoch. The minimum and maximum points of the interval are both inclusive.
struct RoughtimeInterval {
  roughtime::rough_time_t min;
  roughtime::rough_time_t max;
};

// Finds the first min_overlap overlapping intervals from a vector of intervals and returns the
// intersection of these overlapping intervals. An error status will be returned if there are not
// min_overlap overlapping intervals.
oak::StatusOr<RoughtimeInterval> FindOverlap(const std::vector<RoughtimeInterval>& intervals,
                                             const int min_overlap);

}  // namespace oak

#endif  // OAK_SERVER_TIME_ROUGHTIME_UTIL_H_

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

#include "roughtime_util.h"

#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "third_party/asylo/statusor.h"

using ::absl::Status;
using ::oak::StatusOr;

namespace oak {

StatusOr<RoughtimeInterval> FindOverlap(const std::vector<RoughtimeInterval>& intervals,
                                        const int min_overlap) {
  for (const auto& interval : intervals) {
    int count = 0;
    ::roughtime::rough_time_t min = 0;
    ::roughtime::rough_time_t max = UINT64_MAX;
    ::roughtime::rough_time_t point = interval.min;
    for (const auto& test : intervals) {
      if (point >= test.min && point <= test.max) {
        if (test.min > min) {
          min = test.min;
        }
        if (test.max < max) {
          max = test.max;
        }
        ++count;
        if (count == min_overlap) {
          return RoughtimeInterval{min, max};
        }
      }
    }
  }

  return absl::Status(absl::StatusCode::kInternal,
                      absl::StrFormat("Could not find %d overlapping intervals.", min_overlap));
}

}  // namespace oak

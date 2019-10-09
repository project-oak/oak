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

#include "oak/server/labels.h"

#include <algorithm>

namespace oak {

void OakLabels::Merge(const oak::OakLabels& other) {
  // Secrecy tags are a union of the two inputs.
  secrecy_tags.insert(other.secrecy_tags.begin(), other.secrecy_tags.end());

  // Integrity tags are an intersection of the two inputs.
  std::set<std::string> intersection;
  std::set_intersection(this->integrity_tags.begin(), this->integrity_tags.end(),
                        other.integrity_tags.begin(), other.integrity_tags.end(),
                        std::inserter(intersection, intersection.begin()));
  integrity_tags = std::move(intersection);
}

}  // namespace oak

std::ostream& operator<<(std::ostream& os, const oak::OakLabels& labels) {
  os << "secrecy={";
  bool first = true;
  for (const auto& it : labels.secrecy_tags) {
    if (!first) {
      os << ", ";
    }
    first = false;
    os << it;
  }
  os << "}, integrity={";
  first = true;
  for (const auto& it : labels.integrity_tags) {
    if (!first) {
      os << ", ";
    }
    first = false;
    os << it;
  }
  return os << "}";
}

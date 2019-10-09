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

#ifndef OAK_SERVER_LABELS_H_
#define OAK_SERVER_LABELS_H_

#include <iostream>
#include <set>

namespace oak {

struct OakLabels {
  // Merge updates the labels with another instance. Secrecy tags are combined
  // with union, integrity tags are combined with intersection.
  void Merge(const OakLabels& other);

  std::set<std::string> secrecy_tags;
  std::set<std::string> integrity_tags;
};

}  // namespace oak

std::ostream& operator<<(std::ostream& os, const oak::OakLabels& labels);

#endif  // OAK_SERVER_LABELS_H_

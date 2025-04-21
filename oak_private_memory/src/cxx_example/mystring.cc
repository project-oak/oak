//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#include "mystring.h"

#include <algorithm>
#include <functional>
#include <set>
#include <string>
#include <unordered_map>

#include "src/cxx_example/main.rs.h"

namespace oak {
namespace private_memory {
std::unique_ptr<MyString> new_cxx_string(const uint8_t* buff, size_t len) {
  return std::make_unique<MyString>(buff, len);
}

size_t MyString::len() const { return value.size(); }

}  // namespace private_memory
}  // namespace oak

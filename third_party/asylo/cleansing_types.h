/*
 *
 * Copyright 2017 Asylo authors
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
 *
 */

#ifndef ASYLO_UTIL_CLEANSING_TYPES_H_
#define ASYLO_UTIL_CLEANSING_TYPES_H_

#include <string>
#include <vector>

#include "asylo/util/cleansing_allocator.h"

namespace asylo {

/// A string that zeros its memory on free.
///
/// \deprecated Use `CleansingVector` instead.
using CleansingString =
    std::basic_string<char, std::char_traits<char>, CleansingAllocator<char>>;

/// A vector container that zeros its memory on free.
template <typename T>
using CleansingVector = std::vector<T, CleansingAllocator<T>>;

}  // namespace asylo

#endif  // ASYLO_UTIL_CLEANSING_TYPES_H_

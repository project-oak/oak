/*
 *
 * Copyright 2019 Asylo authors
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

#include "asylo/util/statusor.h"

namespace asylo {

#ifdef NDEBUG
const char kValueMoveConstructorMsg[] = "";
const char kValueMoveAssignmentMsg[] = "";
const char kValueOrDieMovedMsg[] = "";
const char kStatusMoveConstructorMsg[] = "";
const char kStatusMoveAssignmentMsg[] = "";
#else
const char kValueMoveConstructorMsg[] =
    "Value moved by StatusOr move constructor";
const char kValueMoveAssignmentMsg[] =
    "Value moved by StatusOr move assignment";
const char kStatusMoveConstructorMsg[] =
    "Status moved by StatusOr move constructor";
const char kValueOrDieMovedMsg[] = "Value moved by StatusOr::ValueOrDie";
const char kStatusMoveAssignmentMsg[] =
    "Status moved by StatusOr move assignment";
#endif

}  // namespace asylo

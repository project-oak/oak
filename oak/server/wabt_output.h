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

#ifndef OAK_SERVER_WABT_OUTPUT_H_
#define OAK_SERVER_WABT_OUTPUT_H_

#include <iostream>

#include "src/interp/interp.h"

/* Output helpers for wabt:: types */

std::ostream& operator<<(std::ostream& os, const wabt::ExternalKind& k);
std::ostream& operator<<(std::ostream& os, const wabt::Type& t);
std::ostream& operator<<(std::ostream& os, const std::vector<wabt::Type>& vt);
std::ostream& operator<<(std::ostream& os, const wabt::interp::FuncSignature& sig);

#endif  // OAK_SERVER_WABT_OUTPUT_H_

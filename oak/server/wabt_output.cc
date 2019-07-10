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

#include "oak/server/wabt_output.h"

std::ostream& operator<<(std::ostream& os, const wabt::ExternalKind& k) {
  return os << wabt::GetKindName(k);
}

std::ostream& operator<<(std::ostream& os, const wabt::Type& t) {
  return os << wabt::GetTypeName(t);
}

std::ostream& operator<<(std::ostream& os, const std::vector<wabt::Type>& vt) {
  os << "(";
  for (size_t ii = 0; ii < vt.size(); ii++) {
    if (ii > 0) {
      os << ", ";
    }
    os << vt[ii];
  }
  return os << ")";
}

std::ostream& operator<<(std::ostream& os, const wabt::interp::FuncSignature& sig) {
  return os << sig.param_types << " -> " << sig.result_types;
}

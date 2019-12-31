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

#ifndef RUST_CHECK_H_
#define RUST_CHECK_H_

// TODO: Using this to temporarily verify rust compat layer is working.

#include <cstdint>

extern "C" {

// TODO(#320): Remove this placeholder when we have some actual functions implemented in Rust and
// used from the C++ side of the Oak Runtime.
int32_t add_magic_number(int32_t x);
};

#endif  // RUST_CHECK_H_

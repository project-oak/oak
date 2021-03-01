/*
 * Copyright 2021 The Project Oak Authors
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

#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <new>
#include <ostream>

namespace oak {

extern "C" {

void generate(const uint8_t* private_key_path_ptr, uintptr_t private_key_path_len,
              const uint8_t* public_key_path_ptr, uintptr_t public_key_path_len);

void sign(const uint8_t* private_key_path_ptr, uintptr_t private_key_path_len,
          const uint8_t* input_string_ptr, uintptr_t input_string_len,
          const uint8_t* signature_file_ptr, uintptr_t signature_file_len);

}  // extern "C"

}  // namespace oak

/*
 * Copyright 2022 The Project Oak Authors
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

#include "tflite_micro.h"

#include <stdint.h>

int main(int argc, char* argv[]) {
  if (tflite_init(nullptr, 0, nullptr, 0) == 0) {
    while (true) {
      tflite_run(nullptr, 0, nullptr, nullptr);
    }
  }

  return 0;
}
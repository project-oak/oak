/* Copyright 2021 The TensorFlow Authors. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
==============================================================================*/

#include "tensorflow/lite/micro/system_setup.h"

#include <ceva-time.h>

#include "tensorflow/lite/micro/micro_time.h"

namespace tflite {

uint32_t ticks_per_second() { return 100e6; }

uint32_t GetCurrentTimeTicks() { return static_cast<uint32_t>(clock()); }

void InitializeTarget() {
  // start clock for profiler
  reset_clock();
  start_clock();
}

}  // namespace tflite

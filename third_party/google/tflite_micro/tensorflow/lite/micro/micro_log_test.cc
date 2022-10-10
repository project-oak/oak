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

#include "tensorflow/lite/micro/micro_log.h"

#include "tensorflow/lite/micro/system_setup.h"

namespace tflite {
inline void InitializeTest() { InitializeTarget(); }
}  // namespace tflite

int main(int argc, char** argv) {
  tflite::InitializeTest();
#ifndef TF_LITE_STRIP_ERROR_STRINGS
  MicroPrintf("Number: %d", 42);
  MicroPrintf("Badly-formed format string %");
  MicroPrintf("Another % badly-formed %% format string");
  MicroPrintf("~~~%s~~~", "ALL TESTS PASSED");
#endif  // !defined(TF_LITE_STRIP_ERROR_STRINGS)
}

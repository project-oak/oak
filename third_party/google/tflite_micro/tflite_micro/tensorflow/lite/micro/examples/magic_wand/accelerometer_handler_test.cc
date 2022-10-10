/* Copyright 2018 The TensorFlow Authors. All Rights Reserved.

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

#include "tensorflow/lite/micro/examples/magic_wand/accelerometer_handler.h"

#include <string.h>

#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestSetup) {
  TfLiteStatus setup_status = SetupAccelerometer();
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, setup_status);
}

TF_LITE_MICRO_TEST(TestAccelerometer) {
  float input[384] = {0.0};
  // Test that the function returns false before insufficient data is available
  bool inference_flag = ReadAccelerometer(input, 384);
  TF_LITE_MICRO_EXPECT_EQ(inference_flag, false);

  // Test that the function returns true once sufficient data is available to
  // fill the model's input buffer (128 sets of values)
  for (int i = 1; i <= 128; i++) {
    inference_flag = ReadAccelerometer(input, 384);
  }
  TF_LITE_MICRO_EXPECT_EQ(inference_flag, true);
}

TF_LITE_MICRO_TESTS_END

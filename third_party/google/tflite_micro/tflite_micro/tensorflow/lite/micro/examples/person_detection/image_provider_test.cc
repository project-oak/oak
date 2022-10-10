/* Copyright 2022 The TensorFlow Authors. All Rights Reserved.

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

#include "tensorflow/lite/micro/examples/person_detection/image_provider.h"

#include <limits>

#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/examples/person_detection/model_settings.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestImageProvider) {
  int8_t image_data[kMaxImageSize];
  TfLiteStatus get_status =
      GetImage(kNumCols, kNumRows, kNumChannels, image_data);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, get_status);

  // Make sure we can read all of the returned memory locations.
  uint32_t total = 0;
  for (int i = 0; i < kMaxImageSize; ++i) {
    total += image_data[i];
  }
  (void)total;
}

TF_LITE_MICRO_TESTS_END

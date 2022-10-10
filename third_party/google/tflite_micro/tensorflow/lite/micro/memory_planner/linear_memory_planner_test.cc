/* Copyright 2019 The TensorFlow Authors. All Rights Reserved.

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

#include "tensorflow/lite/micro/memory_planner/linear_memory_planner.h"

#include "tensorflow/lite/micro/testing/micro_test.h"

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestBasics) {
  tflite::LinearMemoryPlanner planner;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(10, 0, 1));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(20, 1, 2));
  TF_LITE_MICRO_EXPECT_EQ(static_cast<size_t>(30),
                          planner.GetMaximumMemorySize());

  int offset = -1;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.GetOffsetForBuffer(0, &offset));
  TF_LITE_MICRO_EXPECT_EQ(0, offset);

  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.GetOffsetForBuffer(1, &offset));
  TF_LITE_MICRO_EXPECT_EQ(10, offset);
}

TF_LITE_MICRO_TEST(TestErrorHandling) {
  tflite::LinearMemoryPlanner planner;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(10, 0, 1));

  int offset = -1;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteError, planner.GetOffsetForBuffer(1, &offset));
}

TF_LITE_MICRO_TEST(TestPersonDetectionModel) {
  tflite::LinearMemoryPlanner planner;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(9216, 0, 29));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(3, 28, 29));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(256, 27, 28));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(2304, 26, 27));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(2304, 25, 26));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(2304, 24, 25));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(1152, 23, 24));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 22, 23));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 21, 22));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 20, 21));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 19, 20));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 18, 19));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 17, 18));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 16, 17));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 15, 16));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 14, 15));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 13, 14));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 12, 13));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(2304, 11, 12));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(9216, 10, 11));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(9216, 9, 10));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(9216, 8, 9));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(4608, 7, 8));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(18432, 6, 7));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(18432, 5, 6));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(18432, 4, 5));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(9216, 3, 4));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(36864, 2, 3));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(18432, 1, 2));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, planner.AddBuffer(18432, 0, 1));
  TF_LITE_MICRO_EXPECT_EQ(static_cast<size_t>(241027),
                          planner.GetMaximumMemorySize());
}

TF_LITE_MICRO_TESTS_END

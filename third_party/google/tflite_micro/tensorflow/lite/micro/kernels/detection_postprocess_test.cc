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

#include "flatbuffers/flexbuffers.h"
#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/kernels/kernel_runner.h"
#include "tensorflow/lite/micro/test_helpers.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

// See: tensorflow/lite/micro/kernels/detection_postprocess_test/README.md
#include "tensorflow/lite/micro/kernels/detection_postprocess_flexbuffers_generated_data.h"

namespace tflite {
namespace testing {
namespace {

// Common inputs and outputs.

int kInputShape1[] = {3, 1, 6, 4};
int kInputShape2[] = {3, 1, 6, 3};
int kInputShape3[] = {2, 6, 4};
int kOutputShape1[] = {3, 1, 3, 4};
int kOutputShape2[] = {2, 1, 3};
int kOutputShape3[] = {2, 1, 3};
int kOutputShape4[] = {1, 1};

// six boxes in center-size encoding
constexpr float kInputData1[] = {
    0.0, 0.0,  0.0, 0.0,  // box #1
    0.0, 1.0,  0.0, 0.0,  // box #2
    0.0, -1.0, 0.0, 0.0,  // box #3
    0.0, 0.0,  0.0, 0.0,  // box #4
    0.0, 1.0,  0.0, 0.0,  // box #5
    0.0, 0.0,  0.0, 0.0   // box #6
};

// class scores - two classes with background
constexpr float kInputData2[] = {0., .9,  .8,  0., .75, .72, 0., .6, .5,
                                 0., .93, .95, 0., .5,  .4,  0., .3, .2};

// six anchors in center-size encoding
constexpr float kInputData3[] = {
    0.5, 0.5,   1.0, 1.0,  // anchor #1
    0.5, 0.5,   1.0, 1.0,  // anchor #2
    0.5, 0.5,   1.0, 1.0,  // anchor #3
    0.5, 10.5,  1.0, 1.0,  // anchor #4
    0.5, 10.5,  1.0, 1.0,  // anchor #5
    0.5, 100.5, 1.0, 1.0   // anchor #6
};
// Same boxes in box-corner encoding:
// { 0.0, 0.0, 1.0, 1.0,
//   0.0, 0.1, 1.0, 1.1,
//   0.0, -0.1, 1.0, 0.9,
//   0.0, 10.0, 1.0, 11.0,
//   0.0, 10.1, 1.0, 11.1,
//   0.0, 100.0, 1.0, 101.0}

constexpr float kGolden1[] = {0.0, 10.0, 1.0, 11.0,  0.0, 0.0,
                              1.0, 1.0,  0.0, 100.0, 1.0, 101.0};
constexpr float kGolden2[] = {1, 0, 0};
constexpr float kGolden3[] = {0.95, 0.9, 0.3};
constexpr float kGolden4[] = {3.0};

void TestDetectionPostprocess(int* input_dims_data1, const float* input_data1,
                              int* input_dims_data2, const float* input_data2,
                              int* input_dims_data3, const float* input_data3,
                              int* output_dims_data1, float* output_data1,
                              int* output_dims_data2, float* output_data2,
                              int* output_dims_data3, float* output_data3,
                              int* output_dims_data4, float* output_data4,
                              const float* golden1, const float* golden2,
                              const float* golden3, const float* golden4,
                              const float tolerance, bool use_regular_nms) {
  TfLiteIntArray* input_dims1 = IntArrayFromInts(input_dims_data1);
  TfLiteIntArray* input_dims2 = IntArrayFromInts(input_dims_data2);
  TfLiteIntArray* input_dims3 = IntArrayFromInts(input_dims_data3);
  TfLiteIntArray* output_dims1 = IntArrayFromInts(output_dims_data1);
  TfLiteIntArray* output_dims2 = IntArrayFromInts(output_dims_data2);
  TfLiteIntArray* output_dims3 = IntArrayFromInts(output_dims_data3);
  TfLiteIntArray* output_dims4 = IntArrayFromInts(output_dims_data4);

  constexpr int inputs_size = 3;
  constexpr int outputs_size = 4;
  constexpr int tensors_size = inputs_size + outputs_size;

  TfLiteTensor tensors[tensors_size];
  tensors[0] = CreateTensor(input_data1, input_dims1);
  tensors[1] = CreateTensor(input_data2, input_dims2);
  tensors[2] = CreateTensor(input_data3, input_dims3);
  tensors[3] = CreateTensor(output_data1, output_dims1);
  tensors[4] = CreateTensor(output_data2, output_dims2);
  tensors[5] = CreateTensor(output_data3, output_dims3);
  tensors[6] = CreateTensor(output_data4, output_dims4);

  ::tflite::AllOpsResolver resolver;
  const TfLiteRegistration* registration =
      resolver.FindOp("TFLite_Detection_PostProcess");
  TF_LITE_MICRO_EXPECT(registration != nullptr);

  int inputs_array_data[] = {3, 0, 1, 2};
  TfLiteIntArray* inputs_array = IntArrayFromInts(inputs_array_data);
  int outputs_array_data[] = {4, 3, 4, 5, 6};
  TfLiteIntArray* outputs_array = IntArrayFromInts(outputs_array_data);

  micro::KernelRunner runner(*registration, tensors, tensors_size, inputs_array,
                             outputs_array, nullptr);

  // Using generated data as input to operator.
  int data_size = 0;
  const unsigned char* init_data = nullptr;
  if (use_regular_nms) {
    init_data = g_gen_data_regular_nms;
    data_size = g_gen_data_size_regular_nms;
  } else {
    init_data = g_gen_data_none_regular_nms;
    data_size = g_gen_data_size_none_regular_nms;
  }

  // TfLite uses a char* for the raw bytes whereas flexbuffers use an unsigned
  // char*. This small discrepancy results in compiler warnings unless we
  // reinterpret_cast right before passing in the flexbuffer bytes to the
  // KernelRunner.
  TF_LITE_MICRO_EXPECT_EQ(
      kTfLiteOk, runner.InitAndPrepare(reinterpret_cast<const char*>(init_data),
                                       data_size));

  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, runner.Invoke());

  int output_elements_count1 = ElementCount(*tensors[3].dims);
  int output_elements_count2 = ElementCount(*tensors[4].dims);
  int output_elements_count3 = ElementCount(*tensors[5].dims);
  int output_elements_count4 = ElementCount(*tensors[6].dims);

  for (int i = 0; i < output_elements_count1; ++i) {
    TF_LITE_MICRO_EXPECT_NEAR(golden1[i], output_data1[i], tolerance);
  }
  for (int i = 0; i < output_elements_count2; ++i) {
    TF_LITE_MICRO_EXPECT_NEAR(golden2[i], output_data2[i], tolerance);
  }
  for (int i = 0; i < output_elements_count3; ++i) {
    TF_LITE_MICRO_EXPECT_NEAR(golden3[i], output_data3[i], tolerance);
  }
  for (int i = 0; i < output_elements_count4; ++i) {
    TF_LITE_MICRO_EXPECT_NEAR(golden4[i], output_data4[i], tolerance);
  }
}
}  // namespace
}  // namespace testing
}  // namespace tflite

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(DetectionPostprocessFloatFastNMS) {
  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];

  tflite::testing::TestDetectionPostprocess(
      tflite::testing::kInputShape1, tflite::testing::kInputData1,
      tflite::testing::kInputShape2, tflite::testing::kInputData2,
      tflite::testing::kInputShape3, tflite::testing::kInputData3,
      tflite::testing::kOutputShape1, output_data1,
      tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, tflite::testing::kGolden1,
      tflite::testing::kGolden2, tflite::testing::kGolden3,
      tflite::testing::kGolden4,
      /* tolerance */ 0, /* Use regular NMS: */ false);
}

TF_LITE_MICRO_TEST(DetectionPostprocessFloatRegularNMS) {
  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];
  const float kGolden1[] = {0.0, 10.0, 1.0, 11.0, 0.0, 10.0,
                            1.0, 11.0, 0.0, 0.0,  0.0, 0.0};
  const float kGolden3[] = {0.95, 0.9, 0.0};
  const float kGolden4[] = {2.0};

  tflite::testing::TestDetectionPostprocess(
      tflite::testing::kInputShape1, tflite::testing::kInputData1,
      tflite::testing::kInputShape2, tflite::testing::kInputData2,
      tflite::testing::kInputShape3, tflite::testing::kInputData3,
      tflite::testing::kOutputShape1, output_data1,
      tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, kGolden1,
      tflite::testing::kGolden2, kGolden3, kGolden4,
      /* tolerance */ 1e-1, /* Use regular NMS: */ true);
}

TF_LITE_MICRO_TEST(
    DetectionPostprocessFloatFastNMSwithNoBackgroundClassAndKeypoints) {
  int kInputShape1[] = {3, 1, 6, 5};
  int kInputShape2[] = {3, 1, 6, 2};

  // six boxes in center-size encoding
  const float kInputData1[] = {
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #1
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #2
      0.0, -1.0, 0.0, 0.0, 1.0,  // box #3
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #4
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #5
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #6
  };

  // class scores - two classes without background
  const float kInputData2[] = {.9,  .8,  .75, .72, .6, .5,
                               .93, .95, .5,  .4,  .3, .2};

  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];

  tflite::testing::TestDetectionPostprocess(
      kInputShape1, kInputData1, kInputShape2, kInputData2,
      tflite::testing::kInputShape3, tflite::testing::kInputData3,
      tflite::testing::kOutputShape1, output_data1,
      tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, tflite::testing::kGolden1,
      tflite::testing::kGolden2, tflite::testing::kGolden3,
      tflite::testing::kGolden4,
      /* tolerance */ 0, /* Use regular NMS: */ false);
}

TF_LITE_MICRO_TEST(
    DetectionPostprocessFloatRegularNMSwithNoBackgroundClassAndKeypoints) {
  int kInputShape2[] = {3, 1, 6, 2};

  // class scores - two classes without background
  const float kInputData2[] = {.9,  .8,  .75, .72, .6, .5,
                               .93, .95, .5,  .4,  .3, .2};

  const float kGolden1[] = {0.0, 10.0, 1.0, 11.0, 0.0, 10.0,
                            1.0, 11.0, 0.0, 0.0,  0.0, 0.0};
  const float kGolden3[] = {0.95, 0.9, 0.0};
  const float kGolden4[] = {2.0};

  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];

  tflite::testing::TestDetectionPostprocess(
      tflite::testing::kInputShape1, tflite::testing::kInputData1, kInputShape2,
      kInputData2, tflite::testing::kInputShape3, tflite::testing::kInputData3,
      tflite::testing::kOutputShape1, output_data1,
      tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, kGolden1,
      tflite::testing::kGolden2, kGolden3, kGolden4,
      /* tolerance */ 1e-1, /* Use regular NMS: */ true);
}

TF_LITE_MICRO_TEST(
    DetectionPostprocessFloatFastNMSWithBackgroundClassAndKeypoints) {
  int kInputShape1[] = {3, 1, 6, 5};

  // six boxes in center-size encoding
  const float kInputData1[] = {
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #1
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #2
      0.0, -1.0, 0.0, 0.0, 1.0,  // box #3
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #4
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #5
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #6
  };

  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];

  tflite::testing::TestDetectionPostprocess(
      kInputShape1, kInputData1, tflite::testing::kInputShape2,
      tflite::testing::kInputData2, tflite::testing::kInputShape3,
      tflite::testing::kInputData3, tflite::testing::kOutputShape1,
      output_data1, tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, tflite::testing::kGolden1,
      tflite::testing::kGolden2, tflite::testing::kGolden3,
      tflite::testing::kGolden4,
      /* tolerance */ 0, /* Use regular NMS: */ false);
}

TF_LITE_MICRO_TEST(
    DetectionPostprocessFloatFNMSSwithNoBackgroundClassAndKeypointsStableSort) {
  int kInputShape1[] = {3, 1, 6, 5};
  int kInputShape2[] = {3, 1, 6, 2};

  // six boxes in center-size encoding
  const float kInputData1[] = {
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #1
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #2
      0.0, -1.0, 0.0, 0.0, 1.0,  // box #3
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #4
      0.0, 1.0,  0.0, 0.0, 1.0,  // box #5
      0.0, 0.0,  0.0, 0.0, 1.0,  // box #6
  };

  // class scores - two classes without background
  const float kInputData2[] = {0.015625, 0.007812, 0.003906, 0.015625,
                               0.015625, 0.007812, 0.019531, 0.019531,
                               0.007812, 0.003906, 0.003906, 0.003906};
  float output_data1[12];
  float output_data2[3];
  float output_data3[3];
  float output_data4[1];

  const float kGolden2[] = {0, 0, 0};
  const float kGolden3[] = {0.0196078, 0.0156863, 0.00392157};

  tflite::testing::TestDetectionPostprocess(
      kInputShape1, kInputData1, kInputShape2, kInputData2,
      tflite::testing::kInputShape3, tflite::testing::kInputData3,
      tflite::testing::kOutputShape1, output_data1,
      tflite::testing::kOutputShape2, output_data2,
      tflite::testing::kOutputShape3, output_data3,
      tflite::testing::kOutputShape4, output_data4, tflite::testing::kGolden1,
      kGolden2, kGolden3, tflite::testing::kGolden4,
      /* tolerance */ 3e-1, /* Use regular NMS: */ false);
}

TF_LITE_MICRO_TESTS_END

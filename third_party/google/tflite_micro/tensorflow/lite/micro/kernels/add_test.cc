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

#include <cstdint>

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/all_ops_resolver.h"
#include "tensorflow/lite/micro/kernels/kernel_runner.h"
#include "tensorflow/lite/micro/test_helpers.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

namespace tflite {
namespace testing {
namespace {

// Shapes and values for mixed broadcast tests.
constexpr int broadcast_output_dims_count = 36;
constexpr int broadcast_num_shapes = 4;

int broadcast_input1_shape[] = {4, 2, 3, 1, 2};
const float broadcast_input1_values[] = {-0.3, 2.3, 0.9,  0.5, 0.8, -1.1,
                                         1.2,  2.8, -1.6, 0.0, 0.7, -2.2};
const float broadcast_input2_values[] = {0.2, 0.3, -0.4, 0.5, 1.0, 0.9};
const float
    broadcast_goldens[broadcast_num_shapes][broadcast_output_dims_count] = {
        {-0.1, 2.6,  -0.7, 2.8,  0.7,  3.2,  1.1, 0.8,  0.5, 1.0,  1.9, 1.4,
         1.0,  -0.8, 0.4,  -0.6, 1.8,  -0.2, 1.4, 3.1,  0.8, 3.3,  2.2, 3.7,
         -1.4, 0.3,  -2.0, 0.5,  -0.6, 0.9,  0.9, -1.9, 0.3, -1.7, 1.7, -1.3},
        {-0.1, 2.6, 0.5, 1.0, 1.8, -0.2, 1.4, 3.1, -2.0, 0.5, 1.7, -1.3},
        {-0.1, 2.5,  0.0,  2.6,  -0.7, 1.9,  1.1, 0.7,  1.2, 0.8,  0.5, 0.1,
         1.0,  -0.9, 1.1,  -0.8, 0.4,  -1.5, 1.7, 3.3,  2.2, 3.8,  2.1, 3.7,
         -1.1, 0.5,  -0.6, 1.0,  -0.7, 0.9,  1.2, -1.7, 1.7, -1.2, 1.6, -1.3},
        {-0.1, 2.5, 1.2, 0.8, 0.4, -1.5, 1.7, 3.3, -0.6, 1.0, 1.6, -1.3},
};

constexpr int broadcast_max_shape_size = 5;
int broadcast_input2_shapes[broadcast_num_shapes][broadcast_max_shape_size] = {
    {4, 1, 1, 3, 2},
    {4, 1, 3, 1, 2},
    {4, 2, 1, 3, 1},
    {4, 2, 3, 1, 1},
};
int broadcast_output_shapes[broadcast_num_shapes][broadcast_max_shape_size] = {
    {4, 2, 3, 3, 2},
    {4, 2, 3, 1, 2},
    {4, 2, 3, 3, 2},
    {4, 2, 3, 1, 2},
};

template <typename T>
void ValidateAddGoldens(TfLiteTensor* tensors, int tensors_size,
                        const T* golden, T* output, int output_size,
                        TfLiteFusedActivation activation,
                        float tolerance = 1e-5) {
  TfLiteAddParams builtin_data;
  builtin_data.activation = activation;

  int inputs_array_data[] = {2, 0, 1};
  TfLiteIntArray* inputs_array = IntArrayFromInts(inputs_array_data);
  int outputs_array_data[] = {1, 2};
  TfLiteIntArray* outputs_array = IntArrayFromInts(outputs_array_data);

  const TfLiteRegistration registration = Register_ADD();
  micro::KernelRunner runner(registration, tensors, tensors_size, inputs_array,
                             outputs_array, &builtin_data);

  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, runner.InitAndPrepare());
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, runner.Invoke());

  for (int i = 0; i < output_size; ++i) {
    TF_LITE_MICRO_EXPECT_NEAR(golden[i], output[i], tolerance);
  }
}

void TestAddFloat(int* input1_dims_data, const float* input1_data,
                  int* input2_dims_data, const float* input2_data,
                  int* output_dims_data, const float* expected_output,
                  TfLiteFusedActivation activation, float* output_data) {
  TfLiteIntArray* input1_dims = IntArrayFromInts(input1_dims_data);
  TfLiteIntArray* input2_dims = IntArrayFromInts(input2_dims_data);
  TfLiteIntArray* output_dims = IntArrayFromInts(output_dims_data);

  constexpr int inputs_size = 2;
  constexpr int outputs_size = 1;
  constexpr int tensors_size = inputs_size + outputs_size;
  TfLiteTensor tensors[tensors_size] = {
      CreateTensor(input1_data, input1_dims),
      CreateTensor(input2_data, input2_dims),
      CreateTensor(output_data, output_dims),
  };

  ValidateAddGoldens(tensors, tensors_size, expected_output, output_data,
                     ElementCount(*output_dims), activation);
}

template <typename T>
void TestAddQuantized(int* input1_dims_data, const float* input1_data,
                      T* input1_quantized, float input1_scale,
                      int input1_zero_point, int* input2_dims_data,
                      const float* input2_data, T* input2_quantized,
                      float input2_scale, int input2_zero_point,
                      int* output_dims_data, const float* golden,
                      T* golden_quantized, float output_scale,
                      int output_zero_point, TfLiteFusedActivation activation,
                      T* output_data) {
  TfLiteIntArray* input1_dims = IntArrayFromInts(input1_dims_data);
  TfLiteIntArray* input2_dims = IntArrayFromInts(input2_dims_data);
  TfLiteIntArray* output_dims = IntArrayFromInts(output_dims_data);

  constexpr int inputs_size = 2;
  constexpr int outputs_size = 1;
  constexpr int tensors_size = inputs_size + outputs_size;
  TfLiteTensor tensors[tensors_size] = {
      tflite::testing::CreateQuantizedTensor(input1_data, input1_quantized,
                                             input1_dims, input1_scale,
                                             input1_zero_point),
      tflite::testing::CreateQuantizedTensor(input2_data, input2_quantized,
                                             input2_dims, input2_scale,
                                             input2_zero_point),
      tflite::testing::CreateQuantizedTensor(output_data, output_dims,
                                             output_scale, output_zero_point),
  };
  tflite::Quantize(golden, golden_quantized, ElementCount(*output_dims),
                   output_scale, output_zero_point);

  ValidateAddGoldens(tensors, tensors_size, golden_quantized, output_data,
                     ElementCount(*output_dims), activation);
}

}  // namespace
}  // namespace testing
}  // namespace tflite

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(FloatAddNoActivation) {
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8};
  const float input2_values[] = {0.1, 0.2, 0.3, 0.5};
  const float golden_values[] = {-1.9, 0.4, 1.0, 1.3};
  constexpr int output_dims_count = 4;
  float output_data[output_dims_count];
  tflite::testing::TestAddFloat(inout_shape, input1_values, inout_shape,
                                input2_values, inout_shape, golden_values,
                                kTfLiteActNone, output_data);
}

TF_LITE_MICRO_TEST(FloatAddActivationRelu1) {
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8};
  const float input2_values[] = {0.1, 0.2, 0.3, 0.5};
  const float golden_values[] = {-1.0, 0.4, 1.0, 1.0};

  constexpr int output_dims_count = 4;
  float output_data[output_dims_count];
  tflite::testing::TestAddFloat(inout_shape, input1_values, inout_shape,
                                input2_values, inout_shape, golden_values,
                                kTfLiteActReluN1To1, output_data);
}

TF_LITE_MICRO_TEST(FloatAddVariousInputShapes) {
  constexpr int output_dims_count = 6;
  float output_data[output_dims_count];

  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  const float input2_values[] = {0.1, 0.2, 0.3, 0.5, 1.1, 0.1};
  const float expected_output[] = {-1.9, 0.4, 1.0, 1.3, 2.2, 2.1};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  for (int i = 0; i < num_shapes; ++i) {
    tflite::testing::TestAddFloat(test_shapes[i], input1_values, test_shapes[i],
                                  input2_values, test_shapes[i],
                                  expected_output, kTfLiteActNone, output_data);
  }
}

TF_LITE_MICRO_TEST(FloatAddWithScalarBroadcast) {
  constexpr int output_dims_count = 6;
  float output_data[output_dims_count];

  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  int input2_shape[] = {0};
  const float input2_values[] = {0.1};
  const float expected_output[] = {-1.9, 0.3, 0.8, 0.9, 1.2, 2.1};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  for (int i = 0; i < num_shapes; ++i) {
    tflite::testing::TestAddFloat(test_shapes[i], input1_values, input2_shape,
                                  input2_values, test_shapes[i],
                                  expected_output, kTfLiteActNone, output_data);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddNoActivationInt8) {
  const float scales[] = {0.25, 0.5, 1.0};
  const int zero_points[] = {-10, 4, 13};
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.01, -1.01, -0.01, 0.98};
  const float input2_values[] = {1.01, 1.99, 2.99, 4.02};
  const float golden_values[] = {-1, 1, 3, 5};

  constexpr int output_dims_count = 4;
  int8_t input1_quantized[output_dims_count];
  int8_t input2_quantized[output_dims_count];
  int8_t golden_quantized[output_dims_count];
  int8_t output[output_dims_count];

  tflite::testing::TestAddQuantized(
      inout_shape, input1_values, input1_quantized, scales[0], zero_points[0],
      inout_shape, input2_values, input2_quantized, scales[1], zero_points[1],
      inout_shape, golden_values, golden_quantized, scales[2], zero_points[2],
      kTfLiteActNone, output);
}

TF_LITE_MICRO_TEST(QuantizedAddActivationRelu1Int8) {
  const float scales[] = {0.25, 0.5, 1.0};
  const int zero_points[] = {-10, 4, 13};
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.01, -1.01, -0.01, 0.98};
  const float input2_values[] = {1.01, 1.99, 2.99, 4.02};
  const float golden_values[] = {-1, 1, 1, 1};

  constexpr int output_dims_count = 4;
  int8_t input1_quantized[output_dims_count];
  int8_t input2_quantized[output_dims_count];
  int8_t golden_quantized[output_dims_count];
  int8_t output[output_dims_count];

  tflite::testing::TestAddQuantized(
      inout_shape, input1_values, input1_quantized, scales[0], zero_points[0],
      inout_shape, input2_values, input2_quantized, scales[1], zero_points[1],
      inout_shape, golden_values, golden_quantized, scales[2], zero_points[2],
      kTfLiteActReluN1To1, output);
}

TF_LITE_MICRO_TEST(QuantizedAddVariousInputShapesInt8) {
  const float scales[] = {0.1, 0.05, 0.1};
  const int zero_points[] = {-9, 5, 14};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  const float input2_values[] = {0.1, 0.2, 0.3, 0.5, 1.1, 0.1};
  const float golden_values[] = {-1.9, 0.4, 1.0, 1.3, 2.2, 2.1};

  constexpr int output_dims_count = 6;
  int8_t input1_quantized[output_dims_count];
  int8_t input2_quantized[output_dims_count];
  int8_t golden_quantized[output_dims_count];
  int8_t output[output_dims_count];

  for (int i = 0; i < num_shapes; i++) {
    tflite::testing::TestAddQuantized(
        test_shapes[i], input1_values, input1_quantized, scales[0],
        zero_points[0], test_shapes[i], input2_values, input2_quantized,
        scales[1], zero_points[1], test_shapes[i], golden_values,
        golden_quantized, scales[2], zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddWithScalarBroadcastFloat) {
  float output_float[tflite::testing::broadcast_output_dims_count];

  for (int i = 0; i < tflite::testing::broadcast_num_shapes; ++i) {
    tflite::testing::TestAddFloat(tflite::testing::broadcast_input1_shape,
                                  tflite::testing::broadcast_input1_values,
                                  tflite::testing::broadcast_input2_shapes[i],
                                  tflite::testing::broadcast_input2_values,
                                  tflite::testing::broadcast_output_shapes[i],
                                  tflite::testing::broadcast_goldens[i],
                                  kTfLiteActNone, output_float);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddWithScalarBroadcastInt8) {
  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  int input2_shape[] = {0};
  const float input2_values[] = {0.1};
  const float golden[] = {-1.9, 0.3, 0.8, 0.9, 1.2, 2.1};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  const float scales[] = {0.1, 0.05, 0.05};
  const int zero_points[] = {-8, 4, 12};

  constexpr int output_dims_count = 6;
  int8_t input1_quantized[output_dims_count];
  int8_t input2_quantized[output_dims_count];
  int8_t golden_quantized[output_dims_count];
  int8_t output[output_dims_count];

  for (int i = 0; i < num_shapes; ++i) {
    tflite::testing::TestAddQuantized(
        test_shapes[i], input1_values, input1_quantized, scales[0],
        zero_points[0], input2_shape, input2_values, input2_quantized,
        scales[1], zero_points[1], test_shapes[i], golden, golden_quantized,
        scales[2], zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddWithMixedBroadcastInt8) {
  const float scales[] = {0.1, 0.05, 0.1};
  const int zero_points[] = {-10, -5, 7};
  int8_t input1_quantized[tflite::testing::broadcast_output_dims_count];
  int8_t input2_quantized[tflite::testing::broadcast_output_dims_count];
  int8_t golden_quantized[tflite::testing::broadcast_output_dims_count];
  int8_t output[tflite::testing::broadcast_output_dims_count];

  for (int i = 0; i < tflite::testing::broadcast_num_shapes; ++i) {
    tflite::testing::TestAddQuantized(
        tflite::testing::broadcast_input1_shape,
        tflite::testing::broadcast_input1_values, input1_quantized, scales[0],
        zero_points[0], tflite::testing::broadcast_input2_shapes[i],
        tflite::testing::broadcast_input2_values, input2_quantized, scales[1],
        zero_points[1], tflite::testing::broadcast_output_shapes[i],
        tflite::testing::broadcast_goldens[i], golden_quantized, scales[2],
        zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddNoActivationInt16) {
  const float scales[] = {0.25, 0.5, 1.0};
  const int zero_points[] = {0, 0, 0};
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.01, -1.01, -0.01, 0.98};
  const float input2_values[] = {1.01, 2.01, 3.01, 4.02};
  const float golden_values[] = {-1, 1, 3, 5};

  constexpr int output_dims_count = 4;
  int16_t input1_quantized[output_dims_count];
  int16_t input2_quantized[output_dims_count];
  int16_t golden_quantized[output_dims_count];
  int16_t output[output_dims_count];

  tflite::testing::TestAddQuantized(
      inout_shape, input1_values, input1_quantized, scales[0], zero_points[0],
      inout_shape, input2_values, input2_quantized, scales[1], zero_points[1],
      inout_shape, golden_values, golden_quantized, scales[2], zero_points[2],
      kTfLiteActNone, output);
}

TF_LITE_MICRO_TEST(QuantizedAddActivationRelu1Int16) {
  const float scales[] = {0.25, 0.5, 1.0};
  const int zero_points[] = {0, 0, 0};
  int inout_shape[] = {4, 1, 2, 2, 1};
  const float input1_values[] = {-2.01, -1.01, -0.01, 0.98};
  const float input2_values[] = {1.01, 1.99, 2.99, 4.02};
  const float golden_values[] = {-1, 1, 1, 1};

  constexpr int output_dims_count = 4;
  int16_t input1_quantized[output_dims_count];
  int16_t input2_quantized[output_dims_count];
  int16_t golden_quantized[output_dims_count];
  int16_t output[output_dims_count];

  tflite::testing::TestAddQuantized(
      inout_shape, input1_values, input1_quantized, scales[0], zero_points[0],
      inout_shape, input2_values, input2_quantized, scales[1], zero_points[1],
      inout_shape, golden_values, golden_quantized, scales[2], zero_points[2],
      kTfLiteActReluN1To1, output);
}

TF_LITE_MICRO_TEST(QuantizedAddVariousInputShapesInt16) {
  const float scales[] = {0.1, 0.05, 0.1};
  const int zero_points[] = {0, 0, 0};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  const float input2_values[] = {0.1, 0.2, 0.3, 0.5, 1.1, 0.1};
  const float golden_values[] = {-1.9, 0.4, 1.0, 1.3, 2.2, 2.1};

  constexpr int output_dims_count = 6;
  int16_t input1_quantized[output_dims_count];
  int16_t input2_quantized[output_dims_count];
  int16_t golden_quantized[output_dims_count];
  int16_t output[output_dims_count];

  for (int i = 0; i < num_shapes; i++) {
    tflite::testing::TestAddQuantized(
        test_shapes[i], input1_values, input1_quantized, scales[0],
        zero_points[0], test_shapes[i], input2_values, input2_quantized,
        scales[1], zero_points[1], test_shapes[i], golden_values,
        golden_quantized, scales[2], zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddWithScalarBroadcastInt16) {
  const float input1_values[] = {-2.0, 0.2, 0.7, 0.8, 1.1, 2.0};
  int input2_shape[] = {0};
  const float input2_values[] = {0.1};
  const float golden[] = {-1.9, 0.3, 0.8, 0.9, 1.2, 2.1};

  constexpr int num_shapes = 4;
  constexpr int max_shape_size = 5;
  int test_shapes[num_shapes][max_shape_size] = {
      {1, 6},
      {2, 2, 3},
      {3, 2, 1, 3},
      {4, 1, 3, 1, 2},
  };

  const float scales[] = {0.1, 0.05, 0.05};
  const int zero_points[] = {0, 0, 0};

  constexpr int output_dims_count = 6;
  int16_t input1_quantized[output_dims_count];
  int16_t input2_quantized[output_dims_count];
  int16_t golden_quantized[output_dims_count];
  int16_t output[output_dims_count];

  for (int i = 0; i < num_shapes; ++i) {
    tflite::testing::TestAddQuantized(
        test_shapes[i], input1_values, input1_quantized, scales[0],
        zero_points[0], input2_shape, input2_values, input2_quantized,
        scales[1], zero_points[1], test_shapes[i], golden, golden_quantized,
        scales[2], zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TEST(QuantizedAddWithMixedBroadcastInt16) {
  const float scales[] = {0.1, 0.05, 0.1};
  const int zero_points[] = {0, 0, 0};
  int16_t input1_quantized[tflite::testing::broadcast_output_dims_count];
  int16_t input2_quantized[tflite::testing::broadcast_output_dims_count];
  int16_t golden_quantized[tflite::testing::broadcast_output_dims_count];
  int16_t output[tflite::testing::broadcast_output_dims_count];

  for (int i = 0; i < tflite::testing::broadcast_num_shapes; ++i) {
    tflite::testing::TestAddQuantized(
        tflite::testing::broadcast_input1_shape,
        tflite::testing::broadcast_input1_values, input1_quantized, scales[0],
        zero_points[0], tflite::testing::broadcast_input2_shapes[i],
        tflite::testing::broadcast_input2_values, input2_quantized, scales[1],
        zero_points[1], tflite::testing::broadcast_output_shapes[i],
        tflite::testing::broadcast_goldens[i], golden_quantized, scales[2],
        zero_points[2], kTfLiteActNone, output);
  }
}

TF_LITE_MICRO_TESTS_END

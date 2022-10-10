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
/*
 * * Copyright (c) 2021 Cadence Design Systems Inc.
 * *
 * * Permission is hereby granted, free of charge, to any person obtaining
 * * a copy of this software and associated documentation files (the
 * * "Software"), to deal in the Software without restriction, including
 * * without limitation the rights to use, copy, modify, merge, publish,
 * * distribute, sublicense, and/or sell copies of the Software, and to
 * * permit persons to whom the Software is furnished to do so, subject to
 * * the following conditions:
 * *
 * * The above copyright notice and this permission notice shall be included
 * * in all copies or substantial portions of the Software.
 * *
 * * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * */

#include "tensorflow/lite/micro/micro_interpreter.h"
#include "tensorflow/lite/micro/micro_log.h"
#include "tensorflow/lite/micro/micro_mutable_op_resolver.h"
#include "tensorflow/lite/micro/testing/micro_test.h"
#include "tensorflow/lite/schema/schema_generated.h"
#include "third_party/xtensa/examples/micro_speech_lstm/micro_speech_lstm_model_data.h"
#include "third_party/xtensa/examples/micro_speech_lstm/no_micro_features_data.h"
#include "third_party/xtensa/examples/micro_speech_lstm/yes_micro_features_data.h"

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestInvoke) {
  // Map the model into a usable data structure. This doesn't involve any
  // copying or parsing, it's a very lightweight operation.
  const tflite::Model* model =
      ::tflite::GetModel(g_micro_speech_lstm_model_data);
  if (model->version() != TFLITE_SCHEMA_VERSION) {
    MicroPrintf(
        "Model provided is schema version %d not equal "
        "to supported version %d.\n",
        model->version(), TFLITE_SCHEMA_VERSION);
  }

  // Pull in only the operation implementations we need.
  // This relies on a complete list of all the ops needed by this graph.
  // An easier approach is to just use the AllOpsResolver, but this will
  // incur some penalty in code space for op implementations that are not
  // needed by this graph.
  //
  // tflite::AllOpsResolver resolver;
  tflite::MicroMutableOpResolver<4> micro_op_resolver;
  micro_op_resolver.AddUnidirectionalSequenceLSTM();
  micro_op_resolver.AddReshape();
  micro_op_resolver.AddFullyConnected();
  micro_op_resolver.AddSoftmax();

  // Create an area of memory to use for input, output, and intermediate arrays.
  constexpr int tensor_arena_size = 32 * 1024;

  uint8_t tensor_arena[tensor_arena_size];

  // Build an interpreter to run the model with.
  tflite::MicroInterpreter interpreter(model, micro_op_resolver, tensor_arena,
                                       tensor_arena_size);
  interpreter.AllocateTensors();

  // Get information about the memory area to use for the model's input.
  TfLiteTensor* input = interpreter.input(0);

  // Make sure the input has the properties we expect.
  TF_LITE_MICRO_EXPECT_NE(nullptr, input);
  TF_LITE_MICRO_EXPECT_EQ(3, input->dims->size);
  TF_LITE_MICRO_EXPECT_EQ(1, input->dims->data[0]);
  TF_LITE_MICRO_EXPECT_EQ(49, input->dims->data[1]);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteInt8, input->type);

  // Copy a spectrogram created from a .wav audio file of someone saying "Yes",
  // into the memory area used for the input.
  const int8_t* yes_features_data = g_yes_micro_f2e59fea_nohash_1_data;
  for (size_t i = 0; i < input->bytes; ++i) {
    input->data.int8[i] = yes_features_data[i];
  }

  // Run the model on this input and make sure it succeeds.
  TfLiteStatus invoke_status = interpreter.Invoke();
  if (invoke_status != kTfLiteOk) {
    MicroPrintf("Invoke failed\n");
  }
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, invoke_status);

  // Get the output from the model, and make sure it's the expected size and
  // type.
  TfLiteTensor* output = interpreter.output(0);
  TF_LITE_MICRO_EXPECT_EQ(2, output->dims->size);
  TF_LITE_MICRO_EXPECT_EQ(1, output->dims->data[0]);
  TF_LITE_MICRO_EXPECT_EQ(3, output->dims->data[1]);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteInt8, output->type);

  // There are three possible classes in the output, each with a score.
  const int kYesIndex = 0;
  const int kNoIndex = 1;
  const int kUnknownIndex = 2;

  // Make sure that the expected "Yes" score is higher than the other classes.
  uint8_t yes_score = output->data.int8[kYesIndex] + 128;
  uint8_t no_score = output->data.int8[kNoIndex] + 128;
  uint8_t unknown_score = output->data.int8[kUnknownIndex] + 128;
  TF_LITE_MICRO_EXPECT_GT(yes_score, unknown_score);
  TF_LITE_MICRO_EXPECT_GT(yes_score, no_score);

  // Now test with a different input, from a recording of "No".
  const int8_t* no_features_data = g_no_micro_f9643d42_nohash_4_data;
  for (size_t i = 0; i < input->bytes; ++i) {
    input->data.int8[i] = no_features_data[i];
  }

  // Run the model on this "No" input.
  invoke_status = interpreter.Invoke();
  if (invoke_status != kTfLiteOk) {
    MicroPrintf("Invoke failed\n");
  }
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, invoke_status);

  // Get the output from the model, and make sure it's the expected size and
  // type.
  output = interpreter.output(0);
  TF_LITE_MICRO_EXPECT_EQ(2, output->dims->size);
  TF_LITE_MICRO_EXPECT_EQ(1, output->dims->data[0]);
  TF_LITE_MICRO_EXPECT_EQ(3, output->dims->data[1]);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteInt8, output->type);

  // Make sure that the expected "Yes" score is higher than the other classes.
  yes_score = output->data.int8[kYesIndex] + 128;
  no_score = output->data.int8[kNoIndex] + 128;
  unknown_score = output->data.int8[kUnknownIndex] + 128;
  TF_LITE_MICRO_EXPECT_GT(no_score, unknown_score);
  TF_LITE_MICRO_EXPECT_GT(no_score, yes_score);
  MicroPrintf("Ran successfully\n");
}

TF_LITE_MICRO_TESTS_END

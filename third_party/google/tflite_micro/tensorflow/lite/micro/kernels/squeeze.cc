/* Copyright 2020 The TensorFlow Authors. All Rights Reserved.

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

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/quantization_util.h"
#include "tensorflow/lite/kernels/internal/reference/process_broadcast_shapes.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/kernel_util.h"
#include "tensorflow/lite/kernels/op_macros.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/memory_helpers.h"
#include "tensorflow/lite/micro/micro_log.h"

namespace tflite {
namespace {

struct SqueezeContext {
  SqueezeContext(TfLiteContext* context, TfLiteNode* node) {
    params = reinterpret_cast<TfLiteSqueezeParams*>(node->builtin_data);
    micro_context = GetMicroContext(context);
    input = micro_context->AllocateTempInputTensor(node, 0);
    output = micro_context->AllocateTempOutputTensor(node, 0);
  }
  ~SqueezeContext() {
    micro_context->DeallocateTempTfLiteTensor(input);
    micro_context->DeallocateTempTfLiteTensor(output);
  }
  MicroContext* micro_context;
  TfLiteSqueezeParams* params;
  TfLiteTensor* input;
  TfLiteTensor* output;
};

TfLiteStatus Prepare(TfLiteContext* context, TfLiteNode* node) {
  TF_LITE_ENSURE_EQ(context, NumInputs(node), 1);
  TF_LITE_ENSURE_EQ(context, NumOutputs(node), 1);

  SqueezeContext op_context(context, node);
  const int input_num_dims = NumDimensions(op_context.input);
  const int num_squeeze_dims = op_context.params->num_squeeze_dims;

  // Determines number of dimensions of output tensor after squeeze.
  const TfLiteIntArray* input_dims = op_context.input->dims;
  const TfLiteIntArray* output_dims = op_context.output->dims;
  const int* squeeze_dims = op_context.params->squeeze_dims;

  constexpr int max_squeeze_dims = 8;
  TF_LITE_ENSURE(context, input_num_dims <= max_squeeze_dims);
  bool should_squeeze[max_squeeze_dims] = {};

  if (num_squeeze_dims == 0) {
    for (int idx = 0; idx < input_num_dims; ++idx) {
      if (input_dims->data[idx] == 1) {
        should_squeeze[idx] = true;
      }
    }
  } else {
    for (int idx = 0; idx < num_squeeze_dims; ++idx) {
      int current = squeeze_dims[idx] < 0 ? squeeze_dims[idx] + input_num_dims
                                          : squeeze_dims[idx];
      TF_LITE_ENSURE(context, current >= 0 && current < input_num_dims &&
                                  input_dims->data[current] == 1);
      should_squeeze[current] = true;
    }
  }

  // Ensure output dimensions are big enough.
  for (int in_idx = 0, out_idx = 0; in_idx < input_num_dims; ++in_idx) {
    if (!should_squeeze[in_idx]) {
      TFLITE_CHECK_GE(output_dims->data[out_idx++], input_dims->data[in_idx]);
    }
  }

  return kTfLiteOk;
}

TfLiteStatus Eval(TfLiteContext* context, TfLiteNode* node) {
  const TfLiteEvalTensor* input = tflite::micro::GetEvalInput(context, node, 0);

  if (input->type == kTfLiteString) {
    MicroPrintf("Type %s (%d) not supported.", TfLiteTypeGetName(input->type),
                input->type);
    return kTfLiteError;
  }

  TfLiteEvalTensor* output = tflite::micro::GetEvalOutput(context, node, 0);
  size_t input_byte_size;
  size_t output_byte_size;
  TF_LITE_ENSURE_OK(context,
                    TfLiteEvalTensorByteLength(input, &input_byte_size));
  TF_LITE_ENSURE_OK(context,
                    TfLiteEvalTensorByteLength(output, &output_byte_size));

  TF_LITE_ENSURE_EQ(context, input_byte_size, output_byte_size);
  memcpy(output->data.raw, input->data.raw, input_byte_size);
  return kTfLiteOk;
}

}  // namespace

TfLiteRegistration Register_SQUEEZE() {
  return tflite::micro::RegisterOp(nullptr, Prepare, Eval);
}

}  // namespace tflite

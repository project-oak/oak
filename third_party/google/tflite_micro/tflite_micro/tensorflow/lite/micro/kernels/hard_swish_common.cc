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

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/common.h"
#include "tensorflow/lite/kernels/internal/quantization_util.h"
#include "tensorflow/lite/kernels/internal/reference/hard_swish.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/internal/types.h"
#include "tensorflow/lite/kernels/kernel_util.h"
#include "tensorflow/lite/kernels/op_macros.h"
#include "tensorflow/lite/micro/kernels/hard_swish.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/micro_utils.h"

namespace tflite {

const int kHardSwishInputTensor = 0;
const int kHardSwishOutputTensor = 0;

TfLiteStatus HardSwishPrepare(TfLiteContext* context, TfLiteNode* node) {
  MicroContext* micro_context = GetMicroContext(context);

  TFLITE_DCHECK(node->user_data != nullptr);
  TF_LITE_ENSURE_EQ(context, NumInputs(node), 1);
  TF_LITE_ENSURE_EQ(context, NumOutputs(node), 1);

  TfLiteTensor* input =
      micro_context->AllocateTempInputTensor(node, kHardSwishInputTensor);
  TF_LITE_ENSURE(context, input != nullptr);
  TfLiteTensor* output =
      micro_context->AllocateTempOutputTensor(node, kHardSwishOutputTensor);
  TF_LITE_ENSURE(context, output != nullptr);

  if (input->type == kTfLiteInt8) {
    HardSwishParams* params = static_cast<HardSwishParams*>(node->user_data);

    params->input_zero_point = input->params.zero_point;
    params->output_zero_point = output->params.zero_point;

    const float input_scale = input->params.scale;
    const float hires_input_scale = (1.0f / 128.0f) * input_scale;
    const float reluish_scale = 3.0f / 32768.0f;
    const float output_scale = output->params.scale;

    const double output_multiplier =
        static_cast<double>(hires_input_scale / output_scale);
    int32_t output_multiplier_fixedpoint_int32;
    QuantizeMultiplier(output_multiplier, &output_multiplier_fixedpoint_int32,
                       &params->output_multiplier_exponent);
    DownScaleInt32ToInt16Multiplier(
        output_multiplier_fixedpoint_int32,
        &params->output_multiplier_fixedpoint_int16);

    TF_LITE_ENSURE(context, params->output_multiplier_exponent <= 0);

    const double reluish_multiplier =
        static_cast<double>(hires_input_scale / reluish_scale);
    int32_t reluish_multiplier_fixedpoint_int32;
    QuantizeMultiplier(reluish_multiplier, &reluish_multiplier_fixedpoint_int32,
                       &params->reluish_multiplier_exponent);
    DownScaleInt32ToInt16Multiplier(
        reluish_multiplier_fixedpoint_int32,
        &params->reluish_multiplier_fixedpoint_int16);
  }

  micro_context->DeallocateTempTfLiteTensor(input);
  micro_context->DeallocateTempTfLiteTensor(output);

  return kTfLiteOk;
}

}  // namespace tflite

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

#if defined(VISION_P6)

#include <cstdint>

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/common.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/kernel_util.h"
#include "tensorflow/lite/micro/kernels/conv.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/kernels/xtensa/xtensa.h"
#include "tensorflow/lite/micro/kernels/xtensa/xtensa_conv.h"

namespace tflite {

TfLiteStatus ConvPrepareVision(TfLiteContext* context, TfLiteNode* node) {
  TFLITE_DCHECK(node->user_data != nullptr);
  TFLITE_DCHECK(node->builtin_data != nullptr);

  XtensaConvOpData* data = reinterpret_cast<XtensaConvOpData*>(node->user_data);
  const auto& params =
      *(reinterpret_cast<const TfLiteConvParams*>(node->builtin_data));

  MicroContext* micro_context = GetMicroContext(context);
  TfLiteTensor* output =
      micro_context->AllocateTempOutputTensor(node, kConvOutputTensor);
  TF_LITE_ENSURE(context, output != nullptr);
  TfLiteTensor* input =
      micro_context->AllocateTempInputTensor(node, kConvInputTensor);
  TF_LITE_ENSURE(context, input != nullptr);
  TfLiteTensor* filter =
      micro_context->AllocateTempInputTensor(node, kConvWeightsTensor);
  TF_LITE_ENSURE(context, filter != nullptr);
  TfLiteTensor* bias =
      micro_context->AllocateTempInputTensor(node, kConvBiasTensor);
  TF_LITE_ENSURE(context, bias != nullptr);

  const uint32_t input_height = SizeOfDimension(input, 1);
  const uint32_t input_width = SizeOfDimension(input, 2);

  const uint32_t output_height = SizeOfDimension(output, 1);
  const uint32_t output_width = SizeOfDimension(output, 2);

  const uint32_t filter_height = SizeOfDimension(filter, 1);
  const uint32_t filter_width = SizeOfDimension(filter, 2);

  // Dynamically allocate per-channel quantization parameters.
  const int num_channels = SizeOfDimension(filter, kConvQuantizedDimension);
  data->per_channel_output_shift_int8 = static_cast<int8_t*>(
      context->AllocatePersistentBuffer(context, num_channels));

  for (int i = 0; i < num_channels; i++) {
    data->per_channel_output_shift_int8[i] = static_cast<int8_t>(
        -1 * data->reference_op_data.per_channel_output_shift[i]);
  }

  uint32_t context_size = 0;
  uint32_t status = xiConvGetMemReqd_Context(&context_size);
  if (!status && context_size) {
    void* context_data =
        context->AllocatePersistentBuffer(context, context_size);
    if (context_data == nullptr) {
      return kTfLiteError;
    }
    data->p_context = reinterpret_cast<uint8_t*>(context_data);
    data->context_size = context_size;
  }

  const uint32_t input_depth = SizeOfDimension(input, 3);
  const uint32_t output_depth = SizeOfDimension(output, 3);

  status = xiConvSetContext(
      data->p_context, data->context_size, input_depth, input_width,
      input_height, output_depth, output_width, output_height, filter_width,
      filter_height, params.stride_width, input->params.zero_point,
      filter->params.zero_point, output->params.zero_point,
      data->reference_op_data.output_multiplier,
      data->reference_op_data.output_shift,
      data->reference_op_data.output_activation_min,
      data->reference_op_data.output_activation_max,
      (uint8_t*)GetTensorData<uint8_t>(filter),
      data->reference_op_data.padding.width,
      data->reference_op_data.padding.height);
  if (status) {
    return kTfLiteError;
  }

  uint32_t coefficient_size = 0;
  status = xiConvGetMemReqd_Coeff(data->p_context, data->context_size,
                                  &coefficient_size);
  if (status || coefficient_size == 0) {
    return kTfLiteError;
  }

  void* coefficient_data =
      context->AllocatePersistentBuffer(context, coefficient_size);
  if (coefficient_data == nullptr) {
    return kTfLiteError;
  }
  data->reorder_coefficient_bias = reinterpret_cast<int8_t*>(coefficient_data);
  data->reorder_coefficient_bias_size = coefficient_size;

  status = xiConvDoCoeffReorder(
      data->p_context, data->context_size,
      reinterpret_cast<uint8_t*>(data->reorder_coefficient_bias),
      data->reorder_coefficient_bias_size,
      const_cast<uint8_t*>(GetTensorData<uint8_t>(filter)),
      const_cast<int32_t*>(GetTensorData<int32_t>(bias)));
  if (status) {
    return kTfLiteError;
  }

  micro_context->DeallocateTempTfLiteTensor(output);
  micro_context->DeallocateTempTfLiteTensor(input);
  micro_context->DeallocateTempTfLiteTensor(filter);
  micro_context->DeallocateTempTfLiteTensor(bias);

  return kTfLiteOk;
}

TfLiteStatus ConvEvalVision(TfLiteContext* context, TfLiteNode* node,
                            const TfLiteConvParams& params,
                            const XtensaConvOpData& data,
                            const TfLiteEvalTensor* input,
                            const TfLiteEvalTensor* filter,
                            const TfLiteEvalTensor* bias,
                            TfLiteEvalTensor* output) {
  const uint32_t input_size = NumElements(input->dims);
  const uint32_t output_size = NumElements(output->dims);
  const int num_channels = filter->dims->data[kConvQuantizedDimension];

  xiConv(data.p_context, data.context_size,
         const_cast<int8_t*>(tflite::micro::GetTensorData<int8_t>(input)),
         input_size, tflite::micro::GetTensorData<int8_t>(output), output_size,
         data.reorder_coefficient_bias, data.reorder_coefficient_bias_size,
         data.reference_op_data.per_channel_output_multiplier,
         data.per_channel_output_shift_int8, num_channels);
  return kTfLiteOk;
}
}  // namespace tflite
#endif  // defined(VISION_P6)

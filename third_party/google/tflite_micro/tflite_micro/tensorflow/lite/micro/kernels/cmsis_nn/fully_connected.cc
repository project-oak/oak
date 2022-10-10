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

#include "tensorflow/lite/micro/kernels/fully_connected.h"

#include "CMSIS/NN/Include/arm_nnfunctions.h"
#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/common.h"
#include "tensorflow/lite/kernels/internal/quantization_util.h"
#include "tensorflow/lite/kernels/internal/reference/fully_connected.h"
#include "tensorflow/lite/kernels/internal/reference/integer_ops/fully_connected.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/kernel_util.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/micro_log.h"

namespace tflite {
namespace {

struct OpData {
  OpDataFullyConnected reference_op_data;

  // Conv 1x1 that may be invoked in some cases currently need per channel
  // quantization.
  int32_t* per_channel_output_multiplier;
  int32_t* per_channel_output_shift;

  // Index to buffer for optimizations if applicable.
  int buffer_idx;

  int32_t batches;
  int32_t accum_depth;
  int32_t output_depth;
};

void* Init(TfLiteContext* context, const char* buffer, size_t length) {
  TFLITE_DCHECK(context->AllocatePersistentBuffer != nullptr);
  return context->AllocatePersistentBuffer(context, sizeof(OpData));
}

TfLiteStatus Prepare(TfLiteContext* context, TfLiteNode* node) {
  TFLITE_DCHECK(node->user_data != nullptr);
  TFLITE_DCHECK(node->builtin_data != nullptr);

  OpData* data = static_cast<OpData*>(node->user_data);
  const auto params =
      static_cast<const TfLiteFullyConnectedParams*>(node->builtin_data);

  MicroContext* micro_context = GetMicroContext(context);
  TfLiteTensor* input =
      micro_context->AllocateTempInputTensor(node, kFullyConnectedInputTensor);
  TF_LITE_ENSURE(context, input != nullptr);
  TfLiteTensor* filter = micro_context->AllocateTempInputTensor(
      node, kFullyConnectedWeightsTensor);
  TF_LITE_ENSURE(context, filter != nullptr);
  TfLiteTensor* bias =
      micro_context->AllocateTempInputTensor(node, kFullyConnectedBiasTensor);
  TfLiteTensor* output = micro_context->AllocateTempOutputTensor(
      node, kFullyConnectedOutputTensor);
  TF_LITE_ENSURE(context, output != nullptr);

  TF_LITE_ENSURE_TYPES_EQ(context, input->type, output->type);

  const RuntimeShape filter_shape = GetTensorShape(filter);
  const RuntimeShape output_shape = GetTensorShape(output);
  const int filter_dim_count = filter_shape.DimensionsCount();
  const int output_dim_count = output_shape.DimensionsCount();
  cmsis_nn_dims filter_dims;
  filter_dims.n = filter_shape.Dims(filter_dim_count - 1);
  filter_dims.h = 1;
  filter_dims.w = 1;
  filter_dims.c = output_shape.Dims(output_dim_count - 1);

  data->accum_depth = filter_shape.Dims(filter_dim_count - 1);
  data->batches = FlatSizeSkipDim(output_shape, output_dim_count - 1);
  data->output_depth = output_shape.Dims(output_dim_count - 1);

  // Set buffer index to a reset value
  data->buffer_idx = -1;
  TF_LITE_ENSURE_STATUS(CalculateOpDataFullyConnected(
      context, params->activation, input->type, input, filter, bias, output,
      &(data->reference_op_data)));

  int32_t buf_size = 0;

  if (input->type == kTfLiteInt16) {
    TF_LITE_ENSURE_EQ(context, input->params.zero_point, 0);
    TF_LITE_ENSURE_EQ(context, output->params.zero_point, 0);
    buf_size = arm_fully_connected_s16_get_buffer_size(&filter_dims);
  } else if (input->type == kTfLiteInt8) {
    const RuntimeShape input_shape = GetTensorShape(input);

    TFLITE_DCHECK_GE(output_dim_count, 2);
    TFLITE_DCHECK_LE(output_dim_count, 4);

    if (output_dim_count > 2 && data->accum_depth % 4 == 0) {
      data->per_channel_output_multiplier =
          static_cast<int32_t*>(context->AllocatePersistentBuffer(
              context, data->output_depth * sizeof(int32_t)));
      data->per_channel_output_shift =
          static_cast<int32_t*>(context->AllocatePersistentBuffer(
              context, data->output_depth * sizeof(int32_t)));

      cmsis_nn_dims input_dims;
      input_dims.n = data->batches;
      input_dims.h = 1;
      input_dims.w = 1;
      input_dims.c = data->accum_depth;

      buf_size = arm_convolve_1x1_s8_fast_get_buffer_size(&input_dims);
    } else {
      buf_size = arm_fully_connected_s8_get_buffer_size(&filter_dims);
    }
  }

  if (buf_size > 0) {
    TF_LITE_ENSURE_STATUS(context->RequestScratchBufferInArena(
        context, buf_size, &data->buffer_idx));
  }

  micro_context->DeallocateTempTfLiteTensor(output);
  micro_context->DeallocateTempTfLiteTensor(input);
  micro_context->DeallocateTempTfLiteTensor(filter);
  if (bias != nullptr) {
    micro_context->DeallocateTempTfLiteTensor(bias);
  }

  return kTfLiteOk;
}

void PopulateCommonParams(TfLiteContext* context,
                          cmsis_nn_per_tensor_quant_params& quant_params,
                          cmsis_nn_dims& input_dims, cmsis_nn_dims& filter_dims,
                          cmsis_nn_dims& bias_dims, cmsis_nn_dims& output_dims,
                          cmsis_nn_context& ctx, const OpData& data) {
  quant_params.multiplier = data.reference_op_data.output_multiplier;
  quant_params.shift = data.reference_op_data.output_shift;

  input_dims.n = data.batches;
  input_dims.h = 1;
  input_dims.w = 1;
  input_dims.c = data.accum_depth;

  filter_dims.n = data.accum_depth;
  filter_dims.h = 1;
  filter_dims.w = 1;
  filter_dims.c = data.output_depth;

  bias_dims.n = 1;
  bias_dims.h = 1;
  bias_dims.w = 1;
  bias_dims.c = data.output_depth;

  output_dims.n = data.batches;
  output_dims.h = 1;
  output_dims.w = 1;
  output_dims.c = data.output_depth;

  ctx.buf = nullptr;
  ctx.size = 0;
  if (data.buffer_idx > -1) {
    ctx.buf = context->GetScratchBuffer(context, data.buffer_idx);
  }
}

TfLiteStatus EvalQuantizedInt8(TfLiteContext* context, TfLiteNode* node,
                               const OpData& data,
                               const TfLiteEvalTensor* input,
                               const TfLiteEvalTensor* filter,
                               const TfLiteEvalTensor* bias,
                               TfLiteEvalTensor* output) {
  const RuntimeShape output_shape = tflite::micro::GetTensorShape(output);
  const int output_dim_count = output_shape.DimensionsCount();
  TFLITE_DCHECK_GE(output_dim_count, 2);
  TFLITE_DCHECK_LE(output_dim_count, 4);

  cmsis_nn_per_tensor_quant_params quant_params;
  cmsis_nn_dims input_dims;
  cmsis_nn_dims filter_dims;
  cmsis_nn_dims bias_dims;
  cmsis_nn_dims output_dims;
  cmsis_nn_context ctx;

  PopulateCommonParams(context, quant_params, input_dims, filter_dims,
                       bias_dims, output_dims, ctx, data);

  const int32_t* bias_data =
      tflite::micro::GetOptionalTensorData<int32_t>(bias);

  if (output_dim_count > 2 && data.accum_depth % 4 == 0) {
    cmsis_nn_conv_params conv_params;
    conv_params.dilation.h = 1;
    conv_params.dilation.w = 1;
    conv_params.input_offset = -data.reference_op_data.input_zero_point;
    conv_params.output_offset = data.reference_op_data.output_zero_point;
    conv_params.stride.h = 1;
    conv_params.stride.w = 1;
    conv_params.padding.h = 0;
    conv_params.padding.w = 0;
    conv_params.activation.min = data.reference_op_data.output_activation_min;
    conv_params.activation.max = data.reference_op_data.output_activation_max;

    cmsis_nn_per_channel_quant_params per_channel_quant_params;
    per_channel_quant_params.multiplier =
        const_cast<int32_t*>(data.per_channel_output_multiplier);
    per_channel_quant_params.shift =
        const_cast<int32_t*>(data.per_channel_output_shift);

    for (int i = 0; i < data.output_depth; i++) {
      per_channel_quant_params.multiplier[i] = quant_params.multiplier;
      per_channel_quant_params.shift[i] = quant_params.shift;
    }

    TF_LITE_ENSURE_EQ(
        context,
        arm_convolve_1x1_s8_fast(
            &ctx, &conv_params, &per_channel_quant_params, &input_dims,
            tflite::micro::GetTensorData<int8_t>(input), &filter_dims,
            tflite::micro::GetTensorData<int8_t>(filter), &bias_dims, bias_data,
            &output_dims, tflite::micro::GetTensorData<int8_t>(output)),
        ARM_CMSIS_NN_SUCCESS);
  } else {
    cmsis_nn_fc_params fc_params;
    fc_params.input_offset = -data.reference_op_data.input_zero_point;
    fc_params.output_offset = data.reference_op_data.output_zero_point;
    fc_params.filter_offset = 0;
    fc_params.activation.min = data.reference_op_data.output_activation_min;
    fc_params.activation.max = data.reference_op_data.output_activation_max;

    TF_LITE_ENSURE_EQ(
        context,
        arm_fully_connected_s8(
            &ctx, &fc_params, &quant_params, &input_dims,
            tflite::micro::GetTensorData<int8_t>(input), &filter_dims,
            tflite::micro::GetTensorData<int8_t>(filter), &bias_dims, bias_data,
            &output_dims, tflite::micro::GetTensorData<int8_t>(output)),
        ARM_CMSIS_NN_SUCCESS);
  }
  return kTfLiteOk;
}

TfLiteStatus EvalQuantizedInt16(TfLiteContext* context, TfLiteNode* node,
                                const OpData& data,
                                const TfLiteEvalTensor* input,
                                const TfLiteEvalTensor* filter,
                                const TfLiteEvalTensor* bias,
                                TfLiteEvalTensor* output) {
  cmsis_nn_per_tensor_quant_params quant_params;
  cmsis_nn_dims input_dims;
  cmsis_nn_dims filter_dims;
  cmsis_nn_dims bias_dims;
  cmsis_nn_dims output_dims;
  cmsis_nn_context ctx;

  PopulateCommonParams(context, quant_params, input_dims, filter_dims,
                       bias_dims, output_dims, ctx, data);

  const int64_t* bias_data =
      tflite::micro::GetOptionalTensorData<int64_t>(bias);

  cmsis_nn_fc_params fc_params;
  fc_params.input_offset = -data.reference_op_data.input_zero_point;
  fc_params.output_offset = data.reference_op_data.output_zero_point;
  fc_params.filter_offset = 0;
  fc_params.activation.min = data.reference_op_data.output_activation_min;
  fc_params.activation.max = data.reference_op_data.output_activation_max;

  TF_LITE_ENSURE_EQ(
      context,
      arm_fully_connected_s16(
          &ctx, &fc_params, &quant_params, &input_dims,
          tflite::micro::GetTensorData<int16_t>(input), &filter_dims,
          tflite::micro::GetTensorData<int8_t>(filter), &bias_dims, bias_data,
          &output_dims, tflite::micro::GetTensorData<int16_t>(output)),
      ARM_CMSIS_NN_SUCCESS);

  return kTfLiteOk;
}

TfLiteStatus Eval(TfLiteContext* context, TfLiteNode* node) {
  TFLITE_DCHECK(node->builtin_data != nullptr);
  const auto* params =
      static_cast<const TfLiteFullyConnectedParams*>(node->builtin_data);

  const TfLiteEvalTensor* input =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedInputTensor);
  const TfLiteEvalTensor* filter =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedWeightsTensor);
  const TfLiteEvalTensor* bias =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedBiasTensor);
  TfLiteEvalTensor* output =
      tflite::micro::GetEvalOutput(context, node, kFullyConnectedOutputTensor);

  TFLITE_DCHECK(node->user_data != nullptr);
  const OpData& data = *(static_cast<const OpData*>(node->user_data));

  // Checks in Prepare ensure input, output and filter types are all the same.
  switch (input->type) {
    case kTfLiteFloat32: {
      const float* bias_data =
          tflite::micro::GetOptionalTensorData<float>(bias);

      tflite::reference_ops::FullyConnected(
          FullyConnectedParamsFloat(params->activation),
          tflite::micro::GetTensorShape(input),
          tflite::micro::GetTensorData<float>(input),
          tflite::micro::GetTensorShape(filter),
          tflite::micro::GetTensorData<float>(filter),
          tflite::micro::GetTensorShape(bias), bias_data,
          tflite::micro::GetTensorShape(output),
          tflite::micro::GetTensorData<float>(output));
      break;
    }
    case kTfLiteInt8: {
      return EvalQuantizedInt8(context, node, data, input, filter, bias,
                               output);
    }
    case kTfLiteInt16: {
      return EvalQuantizedInt16(context, node, data, input, filter, bias,
                                output);
    }
    default: {
      MicroPrintf("Type %s (%d) not supported.", TfLiteTypeGetName(input->type),
                  input->type);
      return kTfLiteError;
    }
  }
  return kTfLiteOk;
}

// Note that the current function names are not ideal at all (this EvalInt8
// function internally calls EvalQuantizedInt8, and there is similar name
// aliasing in the Eval function too). We will be attempting to have a more
// descriptive naming convention but holding off on that for now, since the
// renaming might be coupled with reducing code duplication and some additional
// refactoring.
TfLiteStatus EvalInt8(TfLiteContext* context, TfLiteNode* node) {
  const TfLiteEvalTensor* input =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedInputTensor);
  const TfLiteEvalTensor* filter =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedWeightsTensor);
  const TfLiteEvalTensor* bias =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedBiasTensor);
  TfLiteEvalTensor* output =
      tflite::micro::GetEvalOutput(context, node, kFullyConnectedOutputTensor);

  TFLITE_DCHECK(node->user_data != nullptr);
  const OpData& data = *(static_cast<const OpData*>(node->user_data));

  // Checks in Prepare ensure input, output and filter types are all the same.
  if (input->type != kTfLiteInt8) {
    MicroPrintf("Type %s (%d) not supported.", TfLiteTypeGetName(input->type),
                input->type);
    return kTfLiteError;
  }

  return EvalQuantizedInt8(context, node, data, input, filter, bias, output);
}

TfLiteStatus EvalInt16(TfLiteContext* context, TfLiteNode* node) {
  const TfLiteEvalTensor* input =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedInputTensor);
  const TfLiteEvalTensor* filter =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedWeightsTensor);
  const TfLiteEvalTensor* bias =
      tflite::micro::GetEvalInput(context, node, kFullyConnectedBiasTensor);
  TfLiteEvalTensor* output =
      tflite::micro::GetEvalOutput(context, node, kFullyConnectedOutputTensor);

  TFLITE_DCHECK(node->user_data != nullptr);
  const OpData& data = *(static_cast<const OpData*>(node->user_data));

  // Checks in Prepare ensure input, output and filter types are all the same.
  if (input->type != kTfLiteInt16) {
    MicroPrintf("Type %s (%d) not supported.", TfLiteTypeGetName(input->type),
                input->type);
    return kTfLiteError;
  }

  return EvalQuantizedInt16(context, node, data, input, filter, bias, output);
}

}  // namespace

TfLiteRegistration Register_FULLY_CONNECTED() {
  return tflite::micro::RegisterOp(Init, Prepare, Eval);
}

TfLiteRegistration Register_FULLY_CONNECTED_INT8() {
  return tflite::micro::RegisterOp(Init, Prepare, EvalInt8);
}

TfLiteRegistration Register_FULLY_CONNECTED_INT16() {
  return tflite::micro::RegisterOp(Init, Prepare, EvalInt16);
}

}  // namespace tflite

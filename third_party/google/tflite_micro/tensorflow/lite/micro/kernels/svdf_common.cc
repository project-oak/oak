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

#include <math.h>

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/common.h"
#include "tensorflow/lite/kernels/internal/quantization_util.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/kernel_util.h"
#include "tensorflow/lite/kernels/op_macros.h"
#include "tensorflow/lite/micro/kernels/activation_utils.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/kernels/svdf.h"
#include "tensorflow/lite/micro/micro_utils.h"

namespace tflite {

/**
 * This version of SVDF is specific to TFLite Micro. It contains the following
 * differences between the TFLite version:
 *
 * 1.) Scratch tensor allocation - scratch tensors must be known ahead of time
 * for the Micro interpreter.
 * 2.) Output dimensions - the TFLite version determines output size and runtime
 * and resizes the output tensor. Micro runtime does not support tensor
 * resizing.
 */

const int kSvdfInputTensor = 0;
const int kSvdfWeightsFeatureTensor = 1;
const int kSvdfWeightsTimeTensor = 2;
const int kSvdfBiasTensor = 3;
const int kSvdfInputActivationStateTensor =
    4;  // This is a variable tensor, and will be modified by this op.
const int kSvdfOutputTensor = 0;

template <typename T>
void EvalIntegerSvdfReference(TfLiteContext* context, TfLiteNode* node,
                              const TfLiteEvalTensor* input_tensor,
                              const TfLiteEvalTensor* weights_feature_tensor,
                              const TfLiteEvalTensor* weights_time_tensor,
                              const TfLiteEvalTensor* bias_tensor,
                              const TfLiteSVDFParams* params,
                              TfLiteEvalTensor* activation_state_tensor,
                              TfLiteEvalTensor* output_tensor,
                              const OpDataSvdf& data) {
  const int n_rank = params->rank;
  const int n_batch = input_tensor->dims->data[0];
  const int n_input = input_tensor->dims->data[1];
  const int n_filter = weights_feature_tensor->dims->data[0];
  const int n_unit = n_filter / n_rank;
  const int n_memory = weights_time_tensor->dims->data[1];

  TFLITE_DCHECK(context != nullptr);
  TFLITE_DCHECK(context->GetScratchBuffer != nullptr);

  int32_t* scratch_tensor = static_cast<int32_t*>(
      context->GetScratchBuffer(context, data.scratch_tensor_index));
  int32_t* scratch_output_tensor = static_cast<int32_t*>(
      context->GetScratchBuffer(context, data.scratch_output_tensor_index));

  // Shift states.
  T* const state_ptr = tflite::micro::GetTensorData<T>(activation_state_tensor);

  // Left shift the activation_state.
  {
    T* new_state_start = state_ptr;
    const T* old_state_start = state_ptr + 1;
    const T* old_state_end = state_ptr + n_batch * n_filter * n_memory;
    while (old_state_start != old_state_end) {
      *new_state_start++ = *old_state_start++;
    }
  }

  // Note: no need to clear the latest activation, matmul is not accumulative.

  // Feature matmul.
  {
    T* state = tflite::micro::GetTensorData<T>(activation_state_tensor);
    const int8_t* input = tflite::micro::GetTensorData<int8_t>(input_tensor);
    const int8_t* weight_feature =
        tflite::micro::GetTensorData<int8_t>(weights_feature_tensor);
    const int32_t output_max = std::numeric_limits<T>::max();
    const int32_t output_min = std::numeric_limits<T>::min();
    T* result_in_batch = state + (n_memory - 1);
    for (int b = 0; b < n_batch; b++) {
      const int8_t* matrix_ptr = weight_feature;
      for (int r = 0; r < n_filter; r++) {
        int32_t dot_prod = 0;
        const int8_t* vector_in_batch = input + b * n_input;
        for (int c = 0; c < n_input; c++) {
          dot_prod +=
              *matrix_ptr++ * (*vector_in_batch++ - data.input_zero_point);
        }
        dot_prod = MultiplyByQuantizedMultiplier(
            dot_prod, data.effective_scale_1_a, data.effective_scale_1_b);
        dot_prod = std::min(std::max(output_min, dot_prod), output_max);
        // The int16 version of the op assumes a zero_point of 0.  This
        // code accounts for the potentially non-zero zero_point for the int8
        // version of the op.
        *result_in_batch = data.activation_state_zero_point + dot_prod;
        result_in_batch += n_memory;
      }
    }
  }

  // Time.
  {
    for (int b = 0; b < n_batch; ++b) {
      int32_t* scratch_ptr_batch = scratch_tensor + b * n_filter;

      // Perform batched vector dot product:
      const T* vector1_ptr =
          tflite::micro::GetTensorData<T>(weights_time_tensor);
      const T* vector2_ptr =
          tflite::micro::GetTensorData<T>(activation_state_tensor) +
          b * n_memory * n_filter;

      for (int i = 0; i < n_filter; i++) {
        *scratch_ptr_batch = 0;
        for (int j = 0; j < n_memory; j++) {
          *scratch_ptr_batch +=
              *vector1_ptr++ *
              (*vector2_ptr++ - data.activation_state_zero_point);
        }
        scratch_ptr_batch++;
      }
    }
  }

  // Reduce, add bias, rescale, activation.
  {
    // Add bias.
    if (bias_tensor) {
      // Vector batch assign:
      const int32_t* bias_data =
          tflite::micro::GetTensorData<int32_t>(bias_tensor);
      for (int i = 0; i < n_batch; ++i) {
        int32_t* output_ptr = scratch_output_tensor + i * n_unit;
        const int32_t* bias_ptr = bias_data;
        for (int j = 0; j < n_unit; ++j) {
          *output_ptr++ = *bias_ptr++;
        }
      }
    } else {
      int32_t* output_ptr = scratch_output_tensor;
      for (int i = 0; i < n_batch * n_unit; ++i) {
        *output_ptr++ = 0;
      }
    }

    // Reduce.
    for (int b = 0; b < n_batch; ++b) {
      int32_t* output_temp_ptr = scratch_output_tensor + b * n_unit;
      int32_t* scratch_ptr_batch = scratch_tensor + b * n_filter;

      // Reduction sum vector
      for (int i = 0; i < n_unit; ++i) {
        for (int j = 0; j < n_rank; ++j) {
          output_temp_ptr[i] += *scratch_ptr_batch++;
        }
      }
    }

    // Rescale.
    const int32_t output_max = std::numeric_limits<int8_t>::max();
    const int32_t output_min = std::numeric_limits<int8_t>::min();
    for (int i = 0; i < n_batch * n_unit; ++i) {
      int32_t x1 = scratch_output_tensor[i];
      int32_t x2 = MultiplyByQuantizedMultiplier(x1, data.effective_scale_2_a,
                                                 data.effective_scale_2_b);
      int32_t x3 = x2 + data.output_zero_point;
      int32_t x4 = std::min(std::max(output_min, x3), output_max);
      tflite::micro::GetTensorData<int8_t>(output_tensor)[i] =
          static_cast<int8_t>(x4);
    }
  }
}

/**
 * Generate two versions of the integer code.  One with int16_t type for the
 * time weights and the activation state, and another one with int8_t for the
 * same.
 */

void EvalInt16SvdfReference(TfLiteContext* context, TfLiteNode* node,
                            const TfLiteEvalTensor* input_tensor,
                            const TfLiteEvalTensor* weights_feature_tensor,
                            const TfLiteEvalTensor* weights_time_tensor,
                            const TfLiteEvalTensor* bias_tensor,
                            const TfLiteSVDFParams* params,
                            TfLiteEvalTensor* activation_state_tensor,
                            TfLiteEvalTensor* output_tensor,
                            const OpDataSvdf& data) {
  EvalIntegerSvdfReference<int16_t>(
      context, node, input_tensor, weights_feature_tensor, weights_time_tensor,
      bias_tensor, params, activation_state_tensor, output_tensor, data);
}

void EvalInt8SvdfReference(TfLiteContext* context, TfLiteNode* node,
                           const TfLiteEvalTensor* input_tensor,
                           const TfLiteEvalTensor* weights_feature_tensor,
                           const TfLiteEvalTensor* weights_time_tensor,
                           const TfLiteEvalTensor* bias_tensor,
                           const TfLiteSVDFParams* params,
                           TfLiteEvalTensor* activation_state_tensor,
                           TfLiteEvalTensor* output_tensor,
                           const OpDataSvdf& data) {
  EvalIntegerSvdfReference<int8_t>(
      context, node, input_tensor, weights_feature_tensor, weights_time_tensor,
      bias_tensor, params, activation_state_tensor, output_tensor, data);
}

static inline void ApplyTimeWeightsBiasAndActivation(
    int batch_size, int memory_size, int num_filters, int num_units, int rank,
    const float* const weights_time_ptr, const float* const bias_ptr,
    TfLiteFusedActivation activation, float* const state_ptr,
    float* const scratch_ptr, float* const output_ptr) {
  // Compute matmul(activation_state, weights_time).
  for (int b = 0; b < batch_size; ++b) {
    // Perform batched vector dot product:
    float* scratch_ptr_batch = scratch_ptr + b * num_filters;
    const float* vector1_ptr = weights_time_ptr;
    const float* vector2_ptr = state_ptr + b * memory_size * num_filters;
    for (int i = 0; i < num_filters; ++i) {
      *scratch_ptr_batch = 0.f;
      for (int j = 0; j < memory_size; ++j) {
        *scratch_ptr_batch += *vector1_ptr++ * *vector2_ptr++;
      }
      scratch_ptr_batch++;
    }
  }

  // Initialize output with bias if provided.
  if (bias_ptr) {
    // VectorBatchVectorAssign
    for (int i = 0; i < batch_size; ++i) {
      float* output_data = output_ptr + i * num_units;
      const float* bias_data = bias_ptr;
      for (int j = 0; j < num_units; ++j) {
        *output_data++ = *bias_data++;
      }
    }
  } else {
    float* output_data = output_ptr;
    for (int i = 0; i < batch_size * num_units; ++i) {
      *output_data++ = 0.0f;
    }
  }

  // Reduction sum.
  for (int b = 0; b < batch_size; ++b) {
    float* output_ptr_batch = output_ptr + b * num_units;
    float* scratch_ptr_batch = scratch_ptr + b * num_filters;

    // Reduction sum vector
    for (int i = 0; i < num_units; ++i) {
      for (int j = 0; j < rank; j++) {
        output_ptr_batch[i] += *scratch_ptr_batch++;
      }
    }
  }

  // Apply activation.
  for (int b = 0; b < batch_size; ++b) {
    float* output_ptr_batch = output_ptr + b * num_units;
    for (int i = 0; i < num_units; ++i) {
      *output_ptr_batch =
          tflite::ops::micro::ActivationValFloat(activation, *output_ptr_batch);
      ++output_ptr_batch;
    }
  }
}

void EvalFloatSvdfReference(
    TfLiteContext* context, TfLiteNode* node, const TfLiteEvalTensor* input,
    const TfLiteEvalTensor* weights_feature,
    const TfLiteEvalTensor* weights_time, const TfLiteEvalTensor* bias,
    const TfLiteSVDFParams* params, int scratch_tensor_index,
    TfLiteEvalTensor* activation_state, TfLiteEvalTensor* output) {
  const int rank = params->rank;
  const int batch_size = input->dims->data[0];
  const int input_size = input->dims->data[1];
  const int num_filters = weights_feature->dims->data[0];
  const int num_units = num_filters / rank;
  const int memory_size = weights_time->dims->data[1];

  const float* weights_feature_ptr =
      tflite::micro::GetTensorData<float>(weights_feature);
  const float* weights_time_ptr =
      tflite::micro::GetTensorData<float>(weights_time);
  const float* bias_ptr = tflite::micro::GetTensorData<float>(bias);
  const float* input_ptr = tflite::micro::GetTensorData<float>(input);

  float* state_ptr = tflite::micro::GetTensorData<float>(activation_state);

  TFLITE_DCHECK(context != nullptr);
  TFLITE_DCHECK(context->GetScratchBuffer != nullptr);

  float* scratch_ptr = static_cast<float*>(
      context->GetScratchBuffer(context, scratch_tensor_index));

  float* output_ptr = tflite::micro::GetTensorData<float>(output);

  // Left shift the activation_state.
  {
    float* new_state_start = state_ptr;
    const float* old_state_start = state_ptr + 1;
    const float* old_state_end =
        state_ptr + batch_size * num_filters * memory_size;
    while (old_state_start != old_state_end) {
      *new_state_start++ = *old_state_start++;
    }
  }

  // Note: no need to clear the latest activation, matmul is not accumulative.

  // Compute conv1d(inputs, weights_feature).
  // The activation_state's rightmost column is used to save current cycle
  // activation. This is achieved by starting at state_ptr[memory_size - 1] and
  // having the stride equal to memory_size.

  // Perform batched matrix vector multiply operation:
  {
    const float* matrix = weights_feature_ptr;
    const float* vector = input_ptr;
    float* result = &state_ptr[memory_size - 1];
    float* result_in_batch = result;
    for (int i = 0; i < batch_size; ++i) {
      const float* matrix_ptr = matrix;
      for (int j = 0; j < num_filters; ++j) {
        float dot_prod = 0.0f;
        const float* vector_in_batch = vector + i * input_size;
        for (int k = 0; k < input_size; ++k) {
          dot_prod += *matrix_ptr++ * *vector_in_batch++;
        }
        *result_in_batch = dot_prod;
        result_in_batch += memory_size;
      }
    }
  }

  ApplyTimeWeightsBiasAndActivation(
      batch_size, memory_size, num_filters, num_units, rank, weights_time_ptr,
      bias_ptr, params->activation, state_ptr, scratch_ptr, output_ptr);
}

TfLiteStatus PrepareSvdf(TfLiteContext* context, TfLiteNode* node) {
  TFLITE_DCHECK(node->builtin_data != nullptr);

  const auto* params = static_cast<const TfLiteSVDFParams*>(node->builtin_data);

  MicroContext* micro_context = GetMicroContext(context);

  // Validate Tensor Inputs (dtype depends on quantization):
  // [0] = Input, {2, batch_size, input_size}
  // [1] = Weights Feature, {2, num_filters, input_size}
  // [2] = Weights Time, {2, num_filters, memory_size}
  // [3] = Bias (optional), {1, num_units}
  // [4] = Activation State (variable),
  //         {2, batch_size, memory_size * num_filters}
  TfLiteTensor* input =
      micro_context->AllocateTempInputTensor(node, kSvdfInputTensor);
  TF_LITE_ENSURE(context, input != nullptr);
  TfLiteTensor* weights_feature =
      micro_context->AllocateTempInputTensor(node, kSvdfWeightsFeatureTensor);
  TF_LITE_ENSURE(context, weights_feature != nullptr);
  TfLiteTensor* weights_time =
      micro_context->AllocateTempInputTensor(node, kSvdfWeightsTimeTensor);
  TF_LITE_ENSURE(context, weights_time != nullptr);
  TfLiteTensor* bias =
      micro_context->AllocateTempInputTensor(node, kSvdfBiasTensor);
  TfLiteTensor* activation_state = micro_context->AllocateTempInputTensor(
      node, kSvdfInputActivationStateTensor);
  TF_LITE_ENSURE(context, activation_state != nullptr);

  // Define input constants based on input tensor definition above:
  const int rank = params->rank;
  const int input_size = input->dims->data[1];
  const int batch_size = input->dims->data[0];
  const int num_filters = weights_feature->dims->data[0];
  TF_LITE_ENSURE_EQ(context, num_filters % rank, 0);
  const int num_units = num_filters / rank;
  const int memory_size = weights_time->dims->data[1];

  // Validate Input Tensor:
  TF_LITE_ENSURE(context,
                 input->type == kTfLiteFloat32 || input->type == kTfLiteInt8);
  TF_LITE_ENSURE_EQ(context, NumDimensions(input), 2);

  // Validate Tensor Output:
  // [0] = float/int8_t, {2, batch_size, num_units}
  TF_LITE_ENSURE_EQ(context, node->outputs->size, 1);
  TfLiteTensor* output =
      micro_context->AllocateTempOutputTensor(node, kSvdfOutputTensor);
  TF_LITE_ENSURE(context, output != nullptr);
  TF_LITE_ENSURE_EQ(context, NumDimensions(output), 2);
  TF_LITE_ENSURE_EQ(context, output->dims->data[0], batch_size);
  TF_LITE_ENSURE_EQ(context, output->dims->data[1], num_units);

  // Validate Weights Feature Input Tensor:
  TF_LITE_ENSURE_EQ(context, NumDimensions(weights_feature), 2);
  TF_LITE_ENSURE_EQ(context, weights_feature->dims->data[1], input_size);

  // Validate Weights Time Input Tensor:
  TF_LITE_ENSURE_EQ(context, NumDimensions(weights_time), 2);
  TF_LITE_ENSURE_EQ(context, weights_time->dims->data[0], num_filters);
  TF_LITE_ENSURE_EQ(context, weights_time->dims->data[1], memory_size);

  // Validate Optional Bias Input Tensor:
  if (bias != nullptr) {
    TF_LITE_ENSURE_EQ(context, bias->dims->data[0], num_units);
  }

  // Validate Activation State Input Tensor:
  TF_LITE_ENSURE_EQ(context, NumDimensions(activation_state), 2);
  TF_LITE_ENSURE_EQ(context, activation_state->dims->data[0], batch_size);
  TF_LITE_ENSURE_EQ(context, activation_state->dims->data[1],
                    memory_size * num_filters);
  // Since is_variable is not part of TFLiteEvalTensor, check is_variable here.
  TF_LITE_ENSURE_EQ(context, activation_state->is_variable, true);

  TF_LITE_ENSURE_EQ(context, node->inputs->size, 5);

  TFLITE_DCHECK(node->user_data != nullptr);
  OpDataSvdf* data = static_cast<OpDataSvdf*>(node->user_data);

  if (input->type == kTfLiteInt8) {
    TF_LITE_ENSURE_EQ(context, weights_feature->type, kTfLiteInt8);
    TF_LITE_ENSURE(context, (weights_time->type == kTfLiteInt16) ||
                                (weights_time->type == kTfLiteInt8));
    TF_LITE_ENSURE(context, (activation_state->type == kTfLiteInt16) ||
                                (activation_state->type == kTfLiteInt8));
    if (bias != nullptr) {
      TF_LITE_ENSURE_EQ(context, bias->type, kTfLiteInt32);
    }

    TF_LITE_ENSURE_TYPES_EQ(context, output->type, kTfLiteInt8);

    const double effective_scale_1 = static_cast<double>(
        input->params.scale * weights_feature->params.scale /
        activation_state->params.scale);
    const double effective_scale_2 =
        static_cast<double>(activation_state->params.scale *
                            weights_time->params.scale / output->params.scale);

    // TODO(b/162018098): Use TF_LITE_ENSURE_NEAR when it is ready.
    TF_LITE_ENSURE(
        context,
        std::abs(static_cast<double>(bias->params.scale) -
                 static_cast<double>(activation_state->params.scale *
                                     weights_time->params.scale)) < 1e-5);

    QuantizeMultiplier(effective_scale_1, &(data->effective_scale_1_a),
                       &(data->effective_scale_1_b));
    QuantizeMultiplier(effective_scale_2, &(data->effective_scale_2_a),
                       &(data->effective_scale_2_b));

    data->input_zero_point = input->params.zero_point;
    data->output_zero_point = output->params.zero_point;
    data->activation_state_zero_point = activation_state->params.zero_point;

    TFLITE_DCHECK(context->RequestScratchBufferInArena != nullptr);

    const TfLiteStatus scratch_status = context->RequestScratchBufferInArena(
        context, batch_size * num_filters * sizeof(int32_t),
        &(data->scratch_tensor_index));
    TF_LITE_ENSURE_OK(context, scratch_status);

    const TfLiteStatus scratch_output_status =
        context->RequestScratchBufferInArena(
            context, batch_size * num_units * sizeof(int32_t),
            &(data->scratch_output_tensor_index));
    TF_LITE_ENSURE_OK(context, scratch_output_status);
  } else {
    TF_LITE_ENSURE_EQ(context, weights_feature->type, kTfLiteFloat32);
    TF_LITE_ENSURE_EQ(context, weights_time->type, kTfLiteFloat32);
    TF_LITE_ENSURE_EQ(context, activation_state->type, kTfLiteFloat32);
    if (bias != nullptr) {
      TF_LITE_ENSURE_EQ(context, bias->type, kTfLiteFloat32);
    }
    TF_LITE_ENSURE_TYPES_EQ(context, output->type, kTfLiteFloat32);

    TFLITE_DCHECK(context->RequestScratchBufferInArena != nullptr);
    const TfLiteStatus scratch_status = context->RequestScratchBufferInArena(
        context, batch_size * num_filters * sizeof(float),
        &(data->scratch_tensor_index));
    TF_LITE_ENSURE_OK(context, scratch_status);
  }

  micro_context->DeallocateTempTfLiteTensor(input);
  micro_context->DeallocateTempTfLiteTensor(weights_feature);
  micro_context->DeallocateTempTfLiteTensor(weights_time);
  micro_context->DeallocateTempTfLiteTensor(activation_state);
  micro_context->DeallocateTempTfLiteTensor(output);
  micro_context->DeallocateTempTfLiteTensor(bias);
  return kTfLiteOk;
}

}  // namespace tflite

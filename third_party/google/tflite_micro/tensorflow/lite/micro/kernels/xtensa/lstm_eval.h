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
#ifndef TENSORFLOW_LITE_KERNELS_LSTM_EVAL_H_
#define TENSORFLOW_LITE_KERNELS_LSTM_EVAL_H_

#include <cstdint>
#include <memory>

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/portable_tensor_utils.h"
#include "tensorflow/lite/kernels/internal/reference/portable_tensor_utils_impl.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"

namespace tflite {
namespace ops {
namespace micro {
namespace lstm_eval {

#if defined(HIFI5)
void calc_cell_state_without_cifg(int16_t* cell_state,
                                  const int16_t* forget_gate,
                                  const int16_t* cell_gate,
                                  const int16_t* input_gate, int shift1,
                                  int shift2, int clip, int num_elms);

void calc_cell_state_with_cifg(int16_t* cell_state, const int16_t* forget_gate,
                               const int16_t* cell_gate, int shift1, int shift2,
                               int clip, int num_elms);

void xa_nn_elm_mul_16x16_asym8s(int8_t* output, const int16_t* input_1,
                                const int16_t* input_2, int32_t multiplier,
                                int32_t shift, int32_t zero_point,
                                int num_elms);
#endif  // defined(HIFI5)

// Pamameters for integer LSTM.
// Consider split this into two Integer Parameters if more fields are added.
struct IntegerLstmParameter {
  int32_t effective_input_to_input_scale_a;
  int effective_input_to_input_scale_b;
  int32_t effective_recurrent_to_input_scale_a;
  int effective_recurrent_to_input_scale_b;
  int32_t effective_cell_to_input_scale_a;
  int effective_cell_to_input_scale_b;
  int32_t effective_input_to_forget_scale_a;
  int effective_input_to_forget_scale_b;
  int32_t effective_recurrent_to_forget_scale_a;
  int effective_recurrent_to_forget_scale_b;
  int32_t effective_cell_to_forget_scale_a;
  int effective_cell_to_forget_scale_b;
  int32_t effective_input_to_cell_scale_a;
  int effective_input_to_cell_scale_b;
  int32_t effective_recurrent_to_cell_scale_a;
  int effective_recurrent_to_cell_scale_b;
  int32_t effective_input_to_output_scale_a;
  int effective_input_to_output_scale_b;
  int32_t effective_recurrent_to_output_scale_a;
  int effective_recurrent_to_output_scale_b;
  int32_t effective_cell_to_output_scale_a;
  int effective_cell_to_output_scale_b;
  int32_t effective_proj_scale_a;
  int effective_proj_scale_b;
  int32_t effective_hidden_scale_a;
  int effective_hidden_scale_b;
  int32_t layer_norm_input_scale_a;
  int layer_norm_input_scale_b;
  int32_t layer_norm_forget_scale_a;
  int layer_norm_forget_scale_b;
  int32_t layer_norm_cell_scale_a;
  int layer_norm_cell_scale_b;
  int32_t layer_norm_output_scale_a;
  int layer_norm_output_scale_b;
  // Quantized clip value for cell and projection. Zero value means no clipping.
  int16_t quantized_cell_clip;
  int8_t quantized_proj_clip;
  int32_t hidden_zp;
  int32_t cell_scale;

  int32_t input_variance_guard;
  int32_t forget_variance_guard;
  int32_t cell_variance_guard;
  int32_t output_variance_guard;

  // Pre-calculate bias + zero_point * weight.
  // Unabled to use temporary tensors since those are used in Prepare() and
  // scratch buffer is only allocated after Preapre().
  std::unique_ptr<int32_t[]> input_to_forget_effective_bias;
  std::unique_ptr<int32_t[]> recurrent_to_forget_effective_bias;
  std::unique_ptr<int32_t[]> input_to_cell_effective_bias;
  std::unique_ptr<int32_t[]> recurrent_to_cell_effective_bias;
  std::unique_ptr<int32_t[]> input_to_output_effective_bias;
  std::unique_ptr<int32_t[]> recurrent_to_output_effective_bias;
  std::unique_ptr<int32_t[]> input_to_input_effective_bias;
  std::unique_ptr<int32_t[]> recurrent_to_input_effective_bias;
  std::unique_ptr<int32_t[]> projection_effective_bias;

  // Scale and zero point for intermediate tensors.
  // Used only in the 8x8_8 case.
  int32_t intermediate_scale_a[8];
  int32_t intermediate_scale_b[8];
  int32_t intermediate_zp[12];
};

TfLiteStatus EvalFloat(const TfLiteEvalTensor* input,
                       const TfLiteEvalTensor* input_to_input_weights,
                       const TfLiteEvalTensor* input_to_forget_weights,
                       const TfLiteEvalTensor* input_to_cell_weights,
                       const TfLiteEvalTensor* input_to_output_weights,
                       const TfLiteEvalTensor* recurrent_to_input_weights,
                       const TfLiteEvalTensor* recurrent_to_forget_weights,
                       const TfLiteEvalTensor* recurrent_to_cell_weights,
                       const TfLiteEvalTensor* recurrent_to_output_weights,
                       const TfLiteEvalTensor* cell_to_input_weights,
                       const TfLiteEvalTensor* cell_to_forget_weights,
                       const TfLiteEvalTensor* cell_to_output_weights,
                       const TfLiteEvalTensor* input_layer_norm_coefficients,
                       const TfLiteEvalTensor* forget_layer_norm_coefficients,
                       const TfLiteEvalTensor* cell_layer_norm_coefficients,
                       const TfLiteEvalTensor* output_layer_norm_coefficients,
                       const TfLiteEvalTensor* aux_input,
                       const TfLiteEvalTensor* aux_input_to_input_weights,
                       const TfLiteEvalTensor* aux_input_to_forget_weights,
                       const TfLiteEvalTensor* aux_input_to_cell_weights,
                       const TfLiteEvalTensor* aux_input_to_output_weights,
                       const TfLiteEvalTensor* input_gate_bias,
                       const TfLiteEvalTensor* forget_gate_bias,
                       const TfLiteEvalTensor* cell_gate_bias,
                       const TfLiteEvalTensor* output_gate_bias,
                       const TfLiteEvalTensor* projection_weights,
                       const TfLiteEvalTensor* projection_bias,
                       const TfLiteLSTMParams* params, bool forward_sequence,
                       bool time_major, int output_offset,
                       TfLiteEvalTensor* scratch_buffer,
                       TfLiteEvalTensor* output_state,
                       TfLiteEvalTensor* cell_state, TfLiteEvalTensor* output);

TfLiteStatus EvalInteger8x8_16(
    TfLiteContext* context, TfLiteNode* node, const TfLiteEvalTensor* input,
    const TfLiteEvalTensor* input_to_input_weights,
    const TfLiteEvalTensor* input_to_forget_weights,
    const TfLiteEvalTensor* input_to_cell_weights,
    const TfLiteEvalTensor* input_to_output_weights,
    const TfLiteEvalTensor* recurrent_to_input_weights,
    const TfLiteEvalTensor* recurrent_to_forget_weights,
    const TfLiteEvalTensor* recurrent_to_cell_weights,
    const TfLiteEvalTensor* recurrent_to_output_weights,
    const TfLiteEvalTensor* cell_to_input_weights,
    const TfLiteEvalTensor* cell_to_forget_weights,
    const TfLiteEvalTensor* cell_to_output_weights,
    const TfLiteEvalTensor* input_layer_norm_coefficients,
    const TfLiteEvalTensor* forget_layer_norm_coefficients,
    const TfLiteEvalTensor* cell_layer_norm_coefficients,
    const TfLiteEvalTensor* output_layer_norm_coefficients,
    const TfLiteEvalTensor* input_gate_bias,
    const TfLiteEvalTensor* forget_gate_bias,
    const TfLiteEvalTensor* cell_gate_bias,
    const TfLiteEvalTensor* output_gate_bias,
    const TfLiteEvalTensor* projection_weights,
    const TfLiteEvalTensor* projection_bias, const TfLiteLSTMParams* params,
    bool forward_sequence, bool time_major,
    const lstm_eval::IntegerLstmParameter* integer_lstm_param,
    TfLiteEvalTensor* output_state, TfLiteEvalTensor* cell_state,
    TfLiteEvalTensor* output, TfLiteEvalTensor* scratch0,
    TfLiteEvalTensor* scratch1, TfLiteEvalTensor* scratch2,
    TfLiteEvalTensor* scratch3, TfLiteEvalTensor* scratch4,
    TfLiteEvalTensor* scratch5);

TfLiteStatus EvalInteger8x8_8(
    const TfLiteEvalTensor* input,
    const TfLiteEvalTensor* input_to_input_weights,
    const TfLiteEvalTensor* input_to_forget_weights,
    const TfLiteEvalTensor* input_to_cell_weights,
    const TfLiteEvalTensor* input_to_output_weights,
    const TfLiteEvalTensor* recurrent_to_input_weights,
    const TfLiteEvalTensor* recurrent_to_forget_weights,
    const TfLiteEvalTensor* recurrent_to_cell_weights,
    const TfLiteEvalTensor* recurrent_to_output_weights,
    const TfLiteEvalTensor* cell_to_input_weights,
    const TfLiteEvalTensor* cell_to_forget_weights,
    const TfLiteEvalTensor* cell_to_output_weights,
    const TfLiteEvalTensor* input_layer_norm_coefficients,
    const TfLiteEvalTensor* forget_layer_norm_coefficients,
    const TfLiteEvalTensor* cell_layer_norm_coefficients,
    const TfLiteEvalTensor* output_layer_norm_coefficients,
    const TfLiteEvalTensor* input_gate_bias,
    const TfLiteEvalTensor* forget_gate_bias,
    const TfLiteEvalTensor* cell_gate_bias,
    const TfLiteEvalTensor* output_gate_bias,
    const TfLiteEvalTensor* projection_weights,
    const TfLiteEvalTensor* projection_bias, const TfLiteLSTMParams* params,
    TfLiteEvalTensor* output_state, TfLiteEvalTensor* cell_state,
    TfLiteEvalTensor* output,
    const lstm_eval::IntegerLstmParameter* integer_lstm_param,
    TfLiteEvalTensor* scratch0, TfLiteEvalTensor* scratch1,
    TfLiteEvalTensor* scratch2, TfLiteEvalTensor* scratch3,
    TfLiteEvalTensor* scratch4, TfLiteEvalTensor* scratch5,
    TfLiteEvalTensor* scratch6, TfLiteEvalTensor* scratch7);

}  // namespace lstm_eval
}  // namespace micro
}  // namespace ops
}  // namespace tflite
#endif  // TENSORFLOW_LITE_KERNELS_LSTM_EVAL_H_

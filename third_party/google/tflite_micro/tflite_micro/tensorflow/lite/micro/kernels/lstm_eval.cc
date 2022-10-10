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
#include "tensorflow/lite/micro/kernels/lstm_eval.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <memory>

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/compatibility.h"
#include "tensorflow/lite/kernels/internal/portable_tensor_utils.h"
#include "tensorflow/lite/kernels/internal/reference/integer_ops/logistic.h"
#include "tensorflow/lite/kernels/internal/reference/integer_ops/tanh.h"
#include "tensorflow/lite/kernels/internal/tensor_ctypes.h"
#include "tensorflow/lite/kernels/op_macros.h"
#include "tensorflow/lite/micro/kernels/kernel_util.h"
#include "tensorflow/lite/micro/kernels/micro_tensor_utils.h"

namespace tflite {
namespace {

void ComputeRowSums(
    int32_t* input_to_input_row_sums, int32_t* input_to_forget_row_sums,
    int32_t* input_to_cell_row_sums, int32_t* input_to_output_row_sums,
    int32_t* aux_input_to_input_row_sums, int32_t* aux_input_to_forget_row_sums,
    int32_t* aux_input_to_cell_row_sums, int32_t* aux_input_to_output_row_sums,
    int32_t* recurrent_to_input_row_sums, int32_t* recurrent_to_forget_row_sums,
    int32_t* recurrent_to_cell_row_sums, int32_t* recurrent_to_output_row_sums,
    int32_t* projection_weights_row_sums, int32_t* row_sums, int n_cell,
    int n_input, int n_aux_input, int n_output,
    const int8_t* input_to_input_weights_ptr,
    const int8_t* input_to_forget_weights_ptr,
    const int8_t* input_to_cell_weights_ptr,
    const int8_t* input_to_output_weights_ptr,
    const int8_t* aux_input_to_input_weights_ptr,
    const int8_t* aux_input_to_forget_weights_ptr,
    const int8_t* aux_input_to_cell_weights_ptr,
    const int8_t* aux_input_to_output_weights_ptr,
    const int8_t* recurrent_to_input_weights_ptr,
    const int8_t* recurrent_to_forget_weights_ptr,
    const int8_t* recurrent_to_cell_weights_ptr,
    const int8_t* recurrent_to_output_weights_ptr,
    const int8_t* projection_weights_ptr, bool use_cifg,
    const float* aux_input_ptr) {
  // Compute the row sums for dequantization
  if (!use_cifg) {
    tflite::tensor_utils::ReductionSumVector(
        input_to_input_weights_ptr, input_to_input_row_sums, n_cell, n_input);
  }
  tflite::tensor_utils::ReductionSumVector(
      input_to_forget_weights_ptr, input_to_forget_row_sums, n_cell, n_input);
  tflite::tensor_utils::ReductionSumVector(
      input_to_cell_weights_ptr, input_to_cell_row_sums, n_cell, n_input);
  tflite::tensor_utils::ReductionSumVector(
      input_to_output_weights_ptr, input_to_output_row_sums, n_cell, n_input);

  if (aux_input_ptr) {
    if (!use_cifg) {
      tflite::tensor_utils::ReductionSumVector(aux_input_to_input_weights_ptr,
                                               aux_input_to_input_row_sums,
                                               n_cell, n_aux_input);
    }
    tflite::tensor_utils::ReductionSumVector(aux_input_to_forget_weights_ptr,
                                             aux_input_to_forget_row_sums,
                                             n_cell, n_aux_input);
    tflite::tensor_utils::ReductionSumVector(aux_input_to_cell_weights_ptr,
                                             aux_input_to_cell_row_sums, n_cell,
                                             n_aux_input);
    tflite::tensor_utils::ReductionSumVector(aux_input_to_output_weights_ptr,
                                             aux_input_to_output_row_sums,
                                             n_cell, n_aux_input);
  }
  if (!use_cifg) {
    tflite::tensor_utils::ReductionSumVector(recurrent_to_input_weights_ptr,
                                             recurrent_to_input_row_sums,
                                             n_cell, n_output);
  }
  tflite::tensor_utils::ReductionSumVector(recurrent_to_forget_weights_ptr,
                                           recurrent_to_forget_row_sums, n_cell,
                                           n_output);
  tflite::tensor_utils::ReductionSumVector(recurrent_to_cell_weights_ptr,
                                           recurrent_to_cell_row_sums, n_cell,
                                           n_output);
  tflite::tensor_utils::ReductionSumVector(recurrent_to_output_weights_ptr,
                                           recurrent_to_output_row_sums, n_cell,
                                           n_output);

  if (projection_weights_ptr != nullptr) {
    tflite::tensor_utils::ReductionSumVector(
        projection_weights_ptr, projection_weights_row_sums, n_output, n_cell);
  }
}

// Calculates a single LSTM gate.
//
// Implements the following formula: (* is matrix multiply)
//   gate = activate(W_input    * input + W_aux       * aux_input   +
//                   W_peephole * cell  + W_recurrent * prev_output + bias)
// with layer norm:
//   gate = activate(W_norm * normalize(...) + bias) // not adding bias inside
//
// Activation is sigmoid except for the "cell" gate (configurable, usually tanh)
//
// Parameters:
// Input vectors (to LSTM):    | Size:                | Optional?
//   input                     | n_input              |
//   aux_input                 | n_aux_input          | y (bidir LSTM)
// Input vectors (persistent states):
//   output_state              | n_output             |
//   cell_state                | n_cell               |
// 'Constant' inputs:
//   input_to_gate_weights     | n_cell * n_input     |
//   aux_input_to_gate_weights | n_cell * n_aux_input | y (bidir LSTM)
//   recurrent_to_gate_weights | n_cell * n_output    |
//   cell_to_gate_weights      | n_cell               | y (peephole)
//   gate_bias                 | n_cell               |
//   layer_norm_coefficients   | n_cell               | y (layer norm)
// Output vector:
//   gate                      | n_cell               |
// Scalar parameters:
//   n_batch                                    - batch size / number of vectors
//   n_input, n_aux_input, n_output, n_cell     - size of vectors.
//   activation                                 - activation to use.
//   is_input_all_zeros, is_aux_input_all_zeros - if input vectors are all zero.
//   use_layer_norm                             - if doing layer norm LSTM.
inline void CalculateLstmGateFloat(
    const float* input, const float* input_to_gate_weights,
    const float* aux_input, const float* aux_input_to_gate_weights,
    const float* output_state, const float* recurrent_to_gate_weights,
    const float* cell_state, const float* cell_to_gate_weights,
    const float* layer_norm_coefficients, const float* gate_bias,
    const int n_batch, const int n_input, const int n_aux_input,
    const int n_output, const int n_cell,
    const TfLiteFusedActivation activation, float* gate,
    const bool is_input_all_zeros, const bool is_aux_input_all_zeros) {
  const bool use_peephole = (cell_to_gate_weights != nullptr);
  const bool use_layer_norm = (layer_norm_coefficients != nullptr);

  // Initialize scratch buffers with bias for regular lstm or initialize with
  // zero for layer norm lstm.
  if (use_layer_norm) {
    memset(gate, 0, n_cell * n_batch * sizeof(float));
  } else {
    tflite::tensor_utils::VectorBatchVectorAssign(gate_bias, n_cell, n_batch,
                                                  gate);
  }
  // For each batch and cell: compute input_weight * input.
  // Skip if input is all zeros.
  if (!is_input_all_zeros) {
    tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
        input_to_gate_weights, n_cell, n_input, input, n_batch, gate);
  }
  // For each batch and cell: compute aux_input_weight * aux_input.
  // Skip if auxiliary input is not available or all zeros.
  if (!is_aux_input_all_zeros) {
    tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
        aux_input_to_gate_weights, n_cell, n_aux_input, aux_input, n_batch,
        gate);
  }
  // For each batch and cell: compute recurrent_weight * output_state.
  tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
      recurrent_to_gate_weights, n_cell, n_output, output_state, n_batch, gate);
  // For each batch and cell: compute cell_weight .* cell_state (peephole LSTM)
  if (use_peephole) {
    tflite::tensor_utils::VectorBatchVectorCwiseProductAccumulate(
        cell_to_gate_weights, n_cell, cell_state, n_batch, gate);
  }
  // Do layer normalization (if layer norm LSTM)
  if (use_layer_norm) {
    tflite::tensor_utils::MeanStddevNormalization(gate, gate, n_cell, n_batch);
    tflite::tensor_utils::VectorBatchVectorCwiseProduct(
        layer_norm_coefficients, n_cell, gate, n_batch, gate);
    tflite::tensor_utils::VectorBatchVectorAdd(gate_bias, n_cell, n_batch,
                                               gate);
  }
  // Apply activation
  tflite::PortableApplyActivationToVector(gate, n_batch * n_cell, activation,
                                          gate);
}

// Updates the LSTM cell state, used by both float and hybrid LSTM versions.
//
// Implements the following formula:
//   cell_state_new = clip(forget_gate * cell_state + input_gate * cell_gate)
//
// With CIFG LSTM, input gate is replaced by (1-forget_gate).
//
// Parameters:
//  - n_batch, n_cell: sizes of vectors
//  - cell_state: input/output vector, size n_batch*n_cell
//  - input_gate: input vector, size n_batch*n_cell.
//  - forget_gate: input/scratch vector, size n_batch*n_cell, modified with CIFG
//  - cell_gate: input vector, size n_batch*n_cell.
//  - use_cifg: use 1-forget_gate instead of input_gate.
//  - clip: if > 0, clip the resulting cell state to [-clip, +clip].
void UpdateLstmCellFloat(int n_batch, int n_cell, float* cell_state,
                         const float* input_gate, float* forget_gate,
                         const float* cell_gate, bool use_cifg, float clip) {
  tflite::tensor_utils::VectorVectorCwiseProduct(forget_gate, cell_state,
                                                 n_batch * n_cell, cell_state);

  if (use_cifg) {
    // With CIFG, input_gate = 1-forget_gate. Use the forget_gate array as
    // scratch, as input_gate array is not allocated in this case. (Be careful
    // not to write to the scratch before reading the forget gate data.)
    float* scratch = forget_gate;
    tflite::tensor_utils::Sub1Vector(forget_gate, n_batch * n_cell, scratch);
    tflite::tensor_utils::VectorVectorCwiseProductAccumulate(
        cell_gate, scratch, n_batch * n_cell, cell_state);
  } else {
    tflite::tensor_utils::VectorVectorCwiseProductAccumulate(
        cell_gate, input_gate, n_batch * n_cell, cell_state);
  }
  if (clip > 0.0f) {
    tflite::tensor_utils::CwiseClipping(cell_state, n_batch * n_cell, clip);
  }
}

// Calculates the output state tensor of an LSTM step.
//
// Implements the following formula:
//   output_no_projection = output_gate .* activate(cell_state)
//     (elementwise vector product)
// If no projection is used:
//   output = output_state = output_no_projection
// With projection:
//   output = output_state = clip(W*output_no_projection + bias)
//
// Output might not have a different 'stride' than n_batch, so we need to copy.
//
// Parameters:
//  - n_batch: batches: the number of distinct vectors in each array.
//  - n_cell, n_output: sizes of vectors.
//  - cell_state, output_gate: input vectors, size n_batch*n_cell.
//  - projection_weights, projection_weights_scale, projection_bias:
//      constant inputs, describing projection matrix and bias.
//  - proj_clip: if > 0, clip the output of the projection.
//  - output_state: output vector, size n_batch*n_output. Must be contigous.
//  - scratch: scratch area, size n_batch*n_cell.
void CalculateLstmOutputFloat(int n_batch, int n_cell, int n_output,
                              const float* cell_state, const float* output_gate,
                              TfLiteFusedActivation activation,
                              const float* projection_weights,
                              const float* projection_bias,
                              const float proj_clip, float* output_state,
                              float* scratch) {
  tflite::PortableApplyActivationToVector(cell_state, n_batch * n_cell,
                                          activation, scratch);
  tflite::tensor_utils::VectorVectorCwiseProduct(output_gate, scratch,
                                                 n_batch * n_cell, scratch);

  const bool use_projection = (projection_weights != nullptr);
  const bool use_projection_bias = (projection_bias != nullptr);

  if (use_projection) {
    if (use_projection_bias) {
      tflite::tensor_utils::VectorBatchVectorAssign(projection_bias, n_output,
                                                    n_batch, output_state);
    } else {
      memset(output_state, 0, n_batch * n_output * sizeof(float));
    }
    tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
        projection_weights, n_output, n_cell, scratch, n_batch, output_state);
    if (proj_clip > 0.0f) {
      tflite::tensor_utils::CwiseClipping(output_state, n_batch * n_output,
                                          proj_clip);
    }
  } else {
    std::memcpy(output_state, scratch, n_batch * n_output * sizeof(float));
  }
}

// Calculates a single LSTM gate, hybrid version.
// Implements the same functionality as CalculateLstmGateFloat.
void CalculateLstmGateHybrid(
    // Input and weights
    const int8_t* input, const float* input_sf, const int32_t* input_zp,
    const int8_t* input_to_gate_weights,
    const uint8_t* input_to_gate_weights_ledger,
    const float input_to_gate_weights_scale, int32_t* input_to_gate_row_sums,
    // Aux input and weights
    const int8_t* aux_input, const float* aux_input_sf,
    const int32_t* aux_input_zp, const int8_t* aux_input_to_gate_weights,
    const float aux_input_to_gate_weights_scale,
    int32_t* aux_input_to_gate_row_sums,
    // Output state and weights
    const int8_t* output_state, const float* output_state_sf,
    const int32_t* output_state_zp, const int8_t* recurrent_to_gate_weights,
    const uint8_t* recurrent_to_gate_weights_ledger,
    const float recurrent_to_gate_weights_scale,
    int32_t* recurrent_to_gate_row_sums,
    // Cell state and weights (peephole LSTM)
    const float* cell_state, const int8_t* cell_to_gate_weights,
    const float cell_to_gate_weights_scale,
    // Layer normalization coefficients (layer norm LSTM) + gate bias
    const float* layer_norm_coefficients, const float* gate_bias,
    // Array sizes
    const int n_batch, const int n_input, const int n_aux_input,
    const int n_output, const int n_cell,
    const TfLiteFusedActivation activation,
    // Output
    float* gate,
    // Parameters for performance optimizations
    const bool is_input_all_zeros, const bool is_aux_input_all_zeros,
    const bool is_output_state_all_zeros, bool* compute_row_sums,
    // Scratch arrays
    float* scratch0,        // size: n_batch
    float* scratch1,        // size: n_cell, only used if peephole LSTM
    float* scales,          // size: n_batch
    int32_t* accum_scratch  // For MatrixBatchVectorMultiplyAccumulate
) {
  const bool use_peephole = (cell_to_gate_weights != nullptr);
  const bool use_layer_norm = (layer_norm_coefficients != nullptr);

  // Initialize scratch buffers with bias for regular lstm or initialize with
  // zero for layer norm lstm.
  if (use_layer_norm) {
    memset(gate, 0, n_cell * n_batch * sizeof(float));
  } else {
    tflite::tensor_utils::VectorBatchVectorAssign(gate_bias, n_cell, n_batch,
                                                  gate);
  }
  // For each batch and cell: compute input_weight * input.
  // Skip if input is all zeros.
  if (!is_input_all_zeros) {
    if (input_to_gate_weights_ledger != nullptr) {
      for (int i = 0; i < n_batch; i++) {
        scales[i] = input_to_gate_weights_scale * input_sf[i];
      }
      tflite::tensor_utils::SparseMatrixBatchVectorMultiplyAccumulate(
          input_to_gate_weights, input_to_gate_weights_ledger, n_cell, n_input,
          input, scales, n_batch, gate);

    } else {
      tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
          input_to_gate_weights, n_cell, n_input, input,
          input_to_gate_weights_scale, input_sf, n_batch, gate,
          /*per_channel_scale=*/nullptr, input_zp, accum_scratch,
          input_to_gate_row_sums, compute_row_sums, scratch0, nullptr);
    }
  }
  // For each batch and cell: compute aux_input_weight * aux_input.
  // Skip if auxiliary input is not available or all zeros.
  if (!is_aux_input_all_zeros) {
    tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
        aux_input_to_gate_weights, n_cell, n_aux_input, aux_input,
        aux_input_to_gate_weights_scale, aux_input_sf, n_batch, gate,
        /*per_channel_scale=*/nullptr, aux_input_zp, accum_scratch,
        aux_input_to_gate_row_sums, compute_row_sums, scratch0, nullptr);
  }
  // For each batch and cell: compute recurrent_weight * output_state.
  // Skip if output state is all zeros.
  if (!is_output_state_all_zeros) {
    if (recurrent_to_gate_weights_ledger != nullptr) {
      for (int i = 0; i < n_batch; i++) {
        scales[i] = recurrent_to_gate_weights_scale * input_sf[i];
      }
      tflite::tensor_utils::SparseMatrixBatchVectorMultiplyAccumulate(
          recurrent_to_gate_weights, recurrent_to_gate_weights_ledger, n_cell,
          n_output, output_state, scales, n_batch, gate);
    } else {
      tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
          recurrent_to_gate_weights, n_cell, n_output, output_state,
          recurrent_to_gate_weights_scale, output_state_sf, n_batch, gate,
          /*per_channel_scale=*/nullptr, output_state_zp, accum_scratch,
          recurrent_to_gate_row_sums, compute_row_sums, scratch0, nullptr);
    }
  }
  // For each batch and cell: compute cell_weight .* cell_state (peephole LSTM)
  if (use_peephole) {
    float* recovered_cell_weights = scratch1;
    tflite::tensor_utils::VectorScalarMultiply(cell_to_gate_weights, n_cell,
                                               cell_to_gate_weights_scale,
                                               recovered_cell_weights);
    tflite::tensor_utils::VectorBatchVectorCwiseProductAccumulate(
        recovered_cell_weights, n_cell, cell_state, n_batch, gate);
  }
  // Do layer normalization (if layer norm LSTM)
  if (use_layer_norm) {
    tflite::tensor_utils::MeanStddevNormalization(gate, gate, n_cell, n_batch);
    tflite::tensor_utils::VectorBatchVectorCwiseProduct(
        layer_norm_coefficients, n_cell, gate, n_batch, gate);
    tflite::tensor_utils::VectorBatchVectorAdd(gate_bias, n_cell, n_batch,
                                               gate);
  }
  // Apply activation
  tflite::PortableApplyActivationToVector(gate, n_cell * n_batch, activation,
                                          gate);
}

// Calculates the output state tensor of an LSTM step. See Float version too.
//
// Parameters:
//  - n_batch: batches: the number of distinct vectors in each array.
//  - n_cell, n_output: sizes of vectors.
//  - cell_state, output_gate: input vectors, size n_batch*n_cell.
//  - projection_weights, projection_weights_scale, projection_bias:
//      constant inputs, describing projection matrix and bias.
//  - proj_clip: if > 0, clip the output of the projection.
//  - output_state: output vector, size n_batch*n_output. Must be contigous.
//  - asymmetric_quantize_inputs: parameter to control quantization.
//  - projection_weights_row_sums, compute_row_sums: Data for optimized
//      MatrixBatchVectorMultiplyAccumulate.
//  - scratch0: scratch area of size n_batch*n_cell
//  - scratch1: scratch area of size n_batch*n_cell
//  - scratch2: scratch area of size n_batch
//  - scratch3: scratch area of size n_batch
//  - scratch4: scratch area used by MatrixBatchVectorMultiplyAccumulate
//  - scales: scratch area of size n_batch
void CalculateLstmOutputHybrid(
    int n_batch, int n_cell, int n_output, const float* cell_state,
    const float* output_gate, TfLiteFusedActivation activation,
    const int8_t* projection_weights, const uint8_t* projection_weights_ledger,
    float projection_weights_scale, const float* projection_bias,
    const float proj_clip, float* output_state, bool asymmetric_quantize_inputs,
    int32_t* projection_weights_row_sums, bool* compute_row_sums,
    float* scratch0, int8_t* scratch1, float* scratch2, int32_t* scratch3,
    int32_t* scratch4, float* scales) {
  tflite::PortableApplyActivationToVector(cell_state, n_batch * n_cell,
                                          activation, scratch0);
  tflite::tensor_utils::VectorVectorCwiseProduct(output_gate, scratch0,
                                                 n_batch * n_cell, scratch0);

  const bool use_projection = (projection_weights != nullptr);
  const bool use_projection_bias = (projection_bias != nullptr);

  if (use_projection) {
    if (use_projection_bias) {
      tflite::tensor_utils::VectorBatchVectorAssign(projection_bias, n_output,
                                                    n_batch, output_state);
    } else {
      memset(output_state, 0, n_batch * n_output * sizeof(float));
    }
    if (!tflite::tensor_utils::IsZeroVector(scratch0, n_batch * n_cell)) {
      // Save quantization and matmul computation for all zero output.
      tflite::tensor_utils::BatchQuantizeFloats(scratch0, n_batch, n_cell,
                                                scratch1, scratch2, scratch3,
                                                asymmetric_quantize_inputs);
      if (projection_weights_ledger != nullptr) {
        for (int i = 0; i < n_batch; i++) {
          scales[i] = projection_weights_scale * scratch2[i];
        }
        tflite::tensor_utils::SparseMatrixBatchVectorMultiplyAccumulate(
            projection_weights, projection_weights_ledger, n_output, n_cell,
            scratch1, scales, n_batch, output_state);
      } else {
        tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
            projection_weights, n_output, n_cell, scratch1,
            projection_weights_scale, scratch2, n_batch, output_state,
            /*per_channel_scale=*/nullptr, scratch3, scratch4,
            projection_weights_row_sums, compute_row_sums, scratch2, nullptr);
      }
    }
    if (proj_clip > 0.0f) {
      tflite::tensor_utils::CwiseClipping(output_state, n_batch * n_output,
                                          proj_clip);
    }
  } else {
    std::memcpy(output_state, scratch0, n_batch * n_output * sizeof(float));
  }
}

// Calculates a single LSTM gate, int8x8_16 version.
// Implements the same functionality as CalculateLstmGateFloat.
void CalculateLstmGateInteger8x8_16(
    // Input and weights
    const int8_t* input, const int8_t* input_to_gate_weights,
    const int32_t* input_to_gate_bias, const int32_t input_to_gate_scale_a,
    const int32_t input_to_gate_scale_b,
    // Output state and weights
    const int8_t* output_state, const int8_t* recurrent_to_gate_weights,
    const int32_t* recurrent_to_gate_bias,
    const int32_t recurrent_to_gate_scale_a,
    const int32_t recurrent_to_gate_scale_b,
    // Cell state and weights
    const int16_t* cell_state, const int16_t* cell_to_gate_weights,
    const int32_t cell_to_gate_scale_a, const int32_t cell_to_gate_scale_b,
    // Layer normalization parameters (layer norm LSTM)
    const int16_t* layer_norm_coefficients, const int32_t* layer_norm_bias,
    const int32_t layer_norm_input_scale_a,
    const int32_t layer_norm_input_scale_b,
    const int32_t layer_norm_variance_guard,
    // Array sizes
    const int n_batch, const int n_input, const int n_output, const int n_cell,
    const TfLiteFusedActivation activation,
    // Output
    int16_t* gate,
    // Parameters for performance optimizations
    // Scratch arrays
    int32_t* scratch5) {
  const bool use_peephole = (cell_to_gate_weights != nullptr);
  const bool use_layer_norm = (layer_norm_coefficients != nullptr);

  // Initialize scratch buffers with zeros. Note that unlike float and hybrid
  // versions, bias is only used in layer normalization.
  memset(gate, 0, n_batch * n_cell * sizeof(int16_t));
  // For each batch and cell: compute input_weight * input.
  tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
      input, input_to_gate_bias, input_to_gate_weights, input_to_gate_scale_a,
      input_to_gate_scale_b, n_batch, n_input, n_cell, 0, scratch5, gate,
      nullptr);
  // Note: no aux_input.

  // For each batch and cell: compute recurrent_weight * output_state.
  tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
      output_state, recurrent_to_gate_bias, recurrent_to_gate_weights,
      recurrent_to_gate_scale_a, recurrent_to_gate_scale_b, n_batch, n_output,
      n_cell, 0, scratch5, gate, nullptr);
  // For each batch and cell: compute cell_weight * cell_state (peephole LSTM)
  if (use_peephole) {
    tflite::tensor_utils::VectorBatchVectorCwiseProductAccumulate(
        cell_to_gate_weights, n_output, cell_state, n_batch,
        cell_to_gate_scale_a, cell_to_gate_scale_b, gate);
  }
  // Do layer normalization (if layer norm LSTM)
  if (use_layer_norm) {
    tflite::tensor_utils::ApplyLayerNorm(
        gate, layer_norm_coefficients, layer_norm_bias,
        layer_norm_input_scale_a, layer_norm_input_scale_b,
        layer_norm_variance_guard, n_batch, n_cell, gate);
  }
  // Apply activation
  switch (activation) {
    case kTfLiteActSigmoid:

      reference_integer_ops::Logistic(
          0 /*data->input_multiplier*/, 0 /*data->input_left_shift */,
          n_batch * n_cell /*NumElements(input->dims)*/,
          gate /* tflite::micro::GetTensorData<int16_t>(input) */,
          gate /*tflite::micro::GetTensorData<int16_t>(output) */);

      break;
    case kTfLiteActTanh: {
      int32_t dims_data = n_batch * n_cell;
      RuntimeShape tanh_inp_shape = RuntimeShape(1, &dims_data);
      reference_integer_ops::Tanh(0, 0, tanh_inp_shape, gate, tanh_inp_shape,
                                  gate);
    } break;
    default:
      // Only Sigmoid or Tanh is used.
      TFLITE_ASSERT_FALSE;
  }
}

// Updates the LSTM cell state, used by both integer LSTM versions.
// Also see UpdateLstmCellFloat.
//
// Parameters:
//  - n_batch, n_cell: sizes of vectors
//  - cell_state: input/output vector, size n_batch*n_cell
//  - cell_state_scale: scaling factor of cell state.
//  - input_gate: input vector, size n_batch*n_cell.
//  - forget_gate: input/scratch vector, size n_batch*n_cell, always modified.
//  - cell_gate: input vector, size n_batch*n_cell.
//  - use_cifg: use 1-forget_gate instead of input_gate.
//  - clip: if > 0, clip the resulting cell state to [-clip, +clip].
void UpdateLstmCellInteger(int n_batch, int n_cell, int16_t* cell_state,
                           int32_t cell_state_scale, const int16_t* input_gate,
                           int16_t* forget_gate, const int16_t* cell_gate,
                           bool use_cifg, int16_t clip) {
  // Use the forget_gate array as scratch, as input_gate array is not allocated
  // in CIFG case. (Be careful not to write to the scratch before reading the
  // forget gate data.)
  int16_t* scratch = forget_gate;

  tflite::tensor_utils::CwiseMul(forget_gate, cell_state, n_batch, n_cell, 15,
                                 cell_state);
  if (use_cifg) {
    tflite::tensor_utils::Sub1Vector(forget_gate, n_batch * n_cell, scratch);
    tflite::tensor_utils::CwiseMul(scratch, cell_gate, n_batch, n_cell,
                                   30 + cell_state_scale, scratch);
  } else {
    tflite::tensor_utils::CwiseMul(input_gate, cell_gate, n_batch, n_cell,
                                   30 + cell_state_scale, scratch);
  }
  tflite::tensor_utils::CwiseAdd(cell_state, scratch, n_batch, n_cell,
                                 cell_state);

  if (clip > 0) {
    tflite::tensor_utils::CwiseClipping(cell_state, n_batch * n_cell, clip);
  }
}

// Calculates the output state tensor of an LSTM step. See Float and hybrid
// versions as well.
//
// Parameters:
//  - n_batch: batches: the number of distinct vectors in each array.
//  - n_cell, n_output: sizes of vectors.
//  - cell_state, output_gate: input vectors, size n_batch*n_cell.
//  - cell_state_scale: scaling of cell_state.
//  - hidden_scale_[a|b]: effective scale of cell_state.*output_gate
//  - hidden_zp: zero_point for cell_state.*output_gate
//  - projection_weights, proj_scale_[a|b], projection_bias:
//      constant inputs, describing projection matrix and bias.
//  - output_state_zp: zero point of output_state. (Input, calibrated value.)
//  - quantized_proj_clip: if > 0, clip the output of the projection.
//  - output_state: output vector, size n_batch*n_output. Must be contigous.
//  - scratch0: scratch area of size n_batch*n_cell
//  - scratch1: scratch area of size n_batch*n_cell
//  - scratch2: scratch area used by MatrixBatchVectorMultiplyAccumulate
void CalculateLstmOutputInteger8x8_16(
    int n_batch, int n_cell, int n_output, int16_t* cell_state,
    int32_t cell_state_scale, const int16_t* output_gate,
    int32_t hidden_scale_a, int32_t hidden_scale_b, int32_t hidden_zp,
    const int8_t* projection_weights, int32_t proj_scale_a,
    int32_t proj_scale_b, const int32_t* projection_bias,
    int32_t output_state_zp, int8_t quantized_proj_clip, int8_t* output_state,
    int16_t* scratch0, int8_t* scratch1, int32_t* scratch2) {
  // Note: unlike float/hybrid, the activation is always Tanh.

  {
    int32_t tanh_input_left_shift = (15 + cell_state_scale) - 3;
    int32_t dims_data = n_batch * n_cell;
    if (tanh_input_left_shift < 0) /* handling negative shift value */
    {
      int32_t i;
      tanh_input_left_shift = -tanh_input_left_shift;
      for (i = 0; i < dims_data; i++) {
        cell_state[i] = cell_state[i] >> tanh_input_left_shift;
      }
      tanh_input_left_shift = 0;
    }
    RuntimeShape tanh_inp_shape = RuntimeShape(1, &dims_data);
    reference_integer_ops::Tanh(0, tanh_input_left_shift, tanh_inp_shape,
                                cell_state, tanh_inp_shape, scratch0);
  }
  tflite::tensor_utils::CwiseMul(output_gate, scratch0, hidden_scale_a,
                                 hidden_scale_b, n_batch, n_cell, hidden_zp,
                                 scratch1);

  const bool use_projection = (projection_weights != nullptr);

  if (use_projection) {
    // Note: no bias like in float/hybrid
    memset(output_state, 0, n_batch * n_output * sizeof(int8_t));
    tflite::tensor_utils::MatrixBatchVectorMultiplyAccumulate(
        scratch1, projection_bias, projection_weights, proj_scale_a,
        proj_scale_b, n_batch, n_cell, n_output, output_state_zp, scratch2,
        output_state, nullptr);
    if (quantized_proj_clip > 0) {
      tflite::tensor_utils::CwiseClipping(output_state, n_batch * n_output,
                                          quantized_proj_clip);
    }
  } else {
    std::memcpy(output_state, scratch1, n_batch * n_output * sizeof(int8_t));
  }
}

// Calculates a single LSTM gate, int8x8_8 version.
// Implements the same functionality as CalculateLstmGateFloat.
void CalculateLstmGateInteger8x8_8(
    // Inputs and weights
    const int8_t* input, int32_t input_zp, const int8_t* input_to_gate_weight,
    const int32_t input_to_gate_scale_a, const int32_t input_to_gate_scale_b,
    const int32_t input_times_weights_scale_a,
    const int32_t input_times_weights_scale_b,
    const int32_t input_times_weights_zp,
    // Output state and weights
    const int8_t* output_state, const int32_t output_state_zp,
    const int8_t* recurrent_to_gate_weight,
    const int32_t recurrent_to_gate_scale_a,
    const int32_t recurrent_to_gate_scale_b,
    const int32_t output_state_times_weights_scale_a,
    const int32_t output_state_times_weights_scale_b,
    const int32_t output_state_times_weights_zp,
    // Layer normalization parameters (layer norm LSTM)
    const int16_t* layer_norm_gate_weight,
    const int32_t layer_norm_gate_scale_a,
    const int32_t layer_norm_gate_scale_b, const int32_t* gate_bias,
    // Array sizes
    const int n_batch, const int n_input, const int n_output, const int n_cell,
    const TfLiteFusedActivation activation,
    // Output
    int16_t* gate,
    // Scratch arrays, both sized n_batch*n_cell
    int8_t* scratch0, int8_t* scratch1) {
  // Multiply input * input_weights => scratch0
  tflite::tensor_utils::MatrixBatchVectorMultiply(
      input, input_zp, input_to_gate_weight, input_to_gate_scale_a,
      input_to_gate_scale_b, n_batch, n_input, n_cell, scratch0,
      input_times_weights_zp);
  // Multiply output_state * recurrent_weights => scratch1
  tflite::tensor_utils::MatrixBatchVectorMultiply(
      output_state, output_state_zp, recurrent_to_gate_weight,
      recurrent_to_gate_scale_a, recurrent_to_gate_scale_b, n_batch, n_output,
      n_cell, scratch1, output_state_times_weights_zp);
  // Add scratch0 + scratch1 => gate
  tflite::tensor_utils::TwoGateSaturatingAdd(
      scratch0, input_times_weights_zp, scratch1, output_state_times_weights_zp,
      input_times_weights_scale_a, input_times_weights_scale_b,
      output_state_times_weights_scale_a, output_state_times_weights_scale_b,
      n_batch, n_cell, gate);
  // Apply layer normalization.
  tflite::tensor_utils::ApplyLayerNormFloat(
      gate, layer_norm_gate_weight, layer_norm_gate_scale_a,
      layer_norm_gate_scale_b, gate_bias, n_batch, n_cell, gate);
  // Apply activation.
  switch (activation) {
    case kTfLiteActSigmoid:
      tflite::tensor_utils::ApplySigmoidFloat(gate, n_batch, n_cell, gate);
      break;
    case kTfLiteActTanh:
      tflite::tensor_utils::ApplyTanhFloat(gate, n_batch, n_cell, -12, gate);
      break;
    default:
      // Only Sigmoid or Tanh is used.
      TFLITE_ASSERT_FALSE;
  }
}

// Calculates the output state tensor of an LSTM step. See Float and hybrid
// versions as well.
//
// Parameters:
//  - n_batch: batches: the number of distinct vectors in each array.
//  - n_cell, n_output: sizes of vectors.
//  - cell_state, output_gate: input vectors, size n_batch*n_cell.
//  - projection_weights, proj_scale_[a|b], projection_bias:
//      constant inputs, describing projection matrix and bias.
//  - output_state_zp: zero point of the output state.
//  - quantized_proj_clip: if > 0, clip the output of the projection.
//  - output_state: output vector, size n_batch*n_output. Must be contigous.
//  - scratch: scratch area of size n_batch*n_cell
void CalculateLstmOutputInteger8x8_8(
    int n_batch, int n_cell, int n_output, const int16_t* cell_state,
    const int16_t* output_gate, const int8_t* projection_weights,
    int32_t proj_scale_a, int32_t proj_scale_b, const int32_t* projection_bias,
    int32_t output_state_zp, int32_t quantized_proj_clip, int8_t* output_state,
    int16_t* scratch) {
  // Note: unlike float/hybrid, the activation is always Tanh.
  tflite::tensor_utils::ApplyTanhFloat(cell_state, n_batch, n_cell, -15,
                                       scratch);
  tflite::tensor_utils::CwiseMul(output_gate, scratch, n_batch, n_cell,
                                 15 + 15 - 15, scratch);
  // Note: no bias like in float/hybrid
  tflite::tensor_utils::MatrixBatchVectorMultiply(
      scratch, projection_weights, proj_scale_a, proj_scale_b, projection_bias,
      n_batch, n_cell, n_output, output_state_zp, output_state);
  if (quantized_proj_clip > 0) {
    tflite::tensor_utils::CwiseClipping(output_state, n_batch * n_output,
                                        quantized_proj_clip);
  }
}

// Performs an LSTM batch inference step for input specified by input_ptr.
// The LSTM cell is specified by the pointers to its weights (*_weights_ptr) and
// biases (*_bias_ptr), and buffers (*_scratch), along with additional
// parameters:
//  - params: various LSTM params including activation, clipping, etc.,
//  - n_batch: size of batch,
//  - n_cell: number of cells (or units),
//  - n_input: the input size,
//  - n_aux_input: the auxiliary input size.
//  - n_output: the output size.
//  - output_batch_leading_dim: the leading dimension of the output buffer.
//
// Input of size 'n_batch * n_input':
//   input_ptr
// Input of size 'n_batch * n_aux_input':
//   aux_input_ptr                     - optional (can be nullptr)
//
// LSTM weights:
// Input weights of size 'n_cell * n_input':
//   input_to_input_weights            - optional
//   input_to_forget_weights
//   input_to_cell_weights
//   input_to_output_weights
// Auxiliary input weights of size 'n_cell * n_aux_input':
//   aux_input_to_input_weights        - optional
//   aux_input_to_forget_weights       - optional
//   aux_input_to_cell_weights         - optional
//   aux_input_to_output_weights       - optional
// Recurrent weights of size 'n_cell * n_output':
//   recurrent_to_input_weights        - optional
//   recurrent_to_forget_weights
//   recurrent_to_cell_weights
//   recurrent_to_input_weights
// Peephole weights of size 'n_cell', representing diagonal matrices.
//   cell_to_input_weights             - optional
//   cell_to_cell_weights              - optional
//   cell_to_output_weights            - optional
// Projection weights of size 'n_output * n_cell'
//   projection_weights_ptr            - optional
// Gate biases of size 'n_cell':
//   input_gate_bias_ptr               - optional
//   forget_gate_bias_ptr
//   cell_gate_bias_ptr
//   output_gate_bias_ptr
//
// Layer norm coefficients of size 'n_cell', representing diagonal matrices.
//   input_layer_norm_coefficients_ptr  - optional
//   forget_layer_norm_coefficients_ptr - optional
//   cell_layer_norm_coefficients_ptr   - optional
//   output_layer_norm_coefficients_ptr - optional
//
// The pointers to the cell and output state and the output are updated.
//
// The pointers input_ptr, aux_input_ptr, and output_ptr point to data aligned
// in batch_major order, and each step processes batch_size many inputs from
// input_ptr, and updates batch_size many cell and output states.
//
// The output_batch_dim is output.shape[-1], i.e. the outermost dimension of the
// output tensor, and in most cases will be equal to n_output. It is usually not
// when we want to store the LSTM output into a slice of the output tensor, e.g.
// for bidirectional LSTMs with merge_outputs. In this case, the batched
// operations cannot be used since they assume that the batched outputs are
// contiguous, and we manually loop over the batched outputs.
inline void LstmStepFloat(
    const float* input_ptr, const float* input_to_input_weights_ptr,
    const float* input_to_forget_weights_ptr,
    const float* input_to_cell_weights_ptr,
    const float* input_to_output_weights_ptr, const float* aux_input_ptr,
    const float* aux_input_to_input_weights_ptr,
    const float* aux_input_to_forget_weights_ptr,
    const float* aux_input_to_cell_weights_ptr,
    const float* aux_input_to_output_weights_ptr,
    const float* recurrent_to_input_weights_ptr,
    const float* recurrent_to_forget_weights_ptr,
    const float* recurrent_to_cell_weights_ptr,
    const float* recurrent_to_output_weights_ptr,
    const float* cell_to_input_weights_ptr,
    const float* cell_to_forget_weights_ptr,
    const float* cell_to_output_weights_ptr,
    const float* input_layer_norm_coefficients_ptr,
    const float* forget_layer_norm_coefficients_ptr,
    const float* cell_layer_norm_coefficients_ptr,
    const float* output_layer_norm_coefficients_ptr,
    const float* input_gate_bias_ptr, const float* forget_gate_bias_ptr,
    const float* cell_gate_bias_ptr, const float* output_gate_bias_ptr,
    const float* projection_weights_ptr, const float* projection_bias_ptr,
    const TfLiteLSTMParams* params, int n_batch, int n_cell, int n_input,
    int n_aux_input, int n_output, int output_batch_leading_dim,
    float* output_state_ptr, float* cell_state_ptr, float* scratch0,
    float* scratch1, float* scratch2, float* scratch3, float* output_ptr) {
  // Since we have already checked that weights are all there or none, we can
  // check the existence of only one to the get the condition.
  const bool use_cifg = (input_to_input_weights_ptr == nullptr);

  // Make named scratch buffers.
  float* input_gate_scratch = scratch0;
  float* forget_gate_scratch = scratch1;
  float* cell_gate_scratch = scratch2;
  float* output_gate_scratch = scratch3;

  // Check if inputs are all zeros so we can skip some computations.
  const bool is_input_all_zeros =
      tflite::tensor_utils::IsZeroVector(input_ptr, n_batch * n_input);
  const bool is_aux_input_all_zeros =
      (aux_input_ptr == nullptr || tflite::tensor_utils::IsZeroVector(
                                       aux_input_ptr, n_batch * n_aux_input));
  if (!use_cifg) {
    // Calculate the input gate. (If not CIFG.)
    CalculateLstmGateFloat(
        input_ptr, input_to_input_weights_ptr, aux_input_ptr,
        aux_input_to_input_weights_ptr, output_state_ptr,
        recurrent_to_input_weights_ptr, cell_state_ptr,
        cell_to_input_weights_ptr, input_layer_norm_coefficients_ptr,
        input_gate_bias_ptr, n_batch, n_input, n_aux_input, n_output, n_cell,
        /*activation=*/kTfLiteActSigmoid, input_gate_scratch,
        is_input_all_zeros, is_aux_input_all_zeros);
  }
  // Calculate the forget gate.
  CalculateLstmGateFloat(
      input_ptr, input_to_forget_weights_ptr, aux_input_ptr,
      aux_input_to_forget_weights_ptr, output_state_ptr,
      recurrent_to_forget_weights_ptr, cell_state_ptr,
      cell_to_forget_weights_ptr, forget_layer_norm_coefficients_ptr,
      forget_gate_bias_ptr, n_batch, n_input, n_aux_input, n_output, n_cell,
      /*activation=*/kTfLiteActSigmoid, forget_gate_scratch, is_input_all_zeros,
      is_aux_input_all_zeros);
  // Calculate the cell update gate.
  CalculateLstmGateFloat(input_ptr, input_to_cell_weights_ptr, aux_input_ptr,
                         aux_input_to_cell_weights_ptr, output_state_ptr,
                         recurrent_to_cell_weights_ptr, /*cell_state=*/nullptr,
                         /*cell_to_gate_weights=*/nullptr,
                         cell_layer_norm_coefficients_ptr, cell_gate_bias_ptr,
                         n_batch, n_input, n_aux_input, n_output, n_cell,
                         params->activation, cell_gate_scratch,
                         is_input_all_zeros, is_aux_input_all_zeros);
  // Update the cell state.
  UpdateLstmCellFloat(n_batch, n_cell, cell_state_ptr, input_gate_scratch,
                      forget_gate_scratch, cell_gate_scratch, use_cifg,
                      params->cell_clip);
  // Calculate output gate.
  CalculateLstmGateFloat(
      input_ptr, input_to_output_weights_ptr, aux_input_ptr,
      aux_input_to_output_weights_ptr, output_state_ptr,
      recurrent_to_output_weights_ptr, cell_state_ptr,
      cell_to_output_weights_ptr, output_layer_norm_coefficients_ptr,
      output_gate_bias_ptr, n_batch, n_input, n_aux_input, n_output, n_cell,
      /*activation=*/kTfLiteActSigmoid, output_gate_scratch, is_input_all_zeros,
      is_aux_input_all_zeros);
  // Update the output state.
  CalculateLstmOutputFloat(n_batch, n_cell, n_output, cell_state_ptr,
                           output_gate_scratch, params->activation,
                           projection_weights_ptr, projection_bias_ptr,
                           params->proj_clip, output_state_ptr, scratch2);
  // Copy output state to the output. Note that the output's rows may not be
  // contiguous (output_batch_leading_dim != n_output).
  for (int b = 0; b < n_batch; b++) {
    std::memcpy(output_ptr + b * output_batch_leading_dim,
                output_state_ptr + b * n_output, n_output * sizeof(float));
  }
}

// Same as above but with quantized weight matrices. In detail:
// Input of size 'n_batch * n_input':
//   input_ptr
// Input of size 'n_batch * n_aux_input':
//   aux_input_ptr                     - optional (can be nullptr)
//
// LSTM weights:
// Quantized input weights of size 'n_cell * n_input':
//   input_to_input_weights            - optional
//   input_to_forget_weights
//   input_to_cell_weights
//   input_to_input_weights
// Quantized auxiliary input weights of size 'n_cell * n_aux_input':
//   aux_input_to_input_weights        - optional
//   aux_input_to_forget_weights       - optional
//   aux_input_to_cell_weights         - optional
//   aux_input_to_output_weights       - optional
// Quantized recurrent weights of size 'n_cell * n_output':
//   recurrent_to_input_weights        - optional
//   recurrent_to_forget_weights
//   recurrent_to_cell_weights
//   recurrent_to_input_weights
// Quantized peephole weights of size 'n_cell', representing diagonal matrices.
//   cell_to_input_weights             - optional
//   cell_to_cell_weights              - optional
//   cell_to_output_weights            - optional
// Quantized projection weights of size 'n_output * n_cell'
//   projection_weights_ptr            - optional
// Weight scales (scalars) for each of the weights above.
//   input_to_input_weights_scale      - optional
//   input_to_forget_weights_scale
//   input_to_cell_weights_scale
//   input_to_output_weights_scale
//   aux_input_to_input_weights_scale  - optional
//   aux_input_to_forget_weights_scale - optional
//   aux_input_to_cell_weights_scale   - optional
//   aux_input_to_output_weights_scale - optional
//   recurrent_to_input_weights_scale  - optional
//   recurrent_to_forget_weights_scale
//   recurrent_to_cell_weights_scale
//   recurrent_to_output_weights_scale
//   cell_to_input_weights_scale,
//   cell_to_forget_weights_scale,
//   cell_to_output_weights_scale,
//   projection_weights_scale          - optional
// Gate biases of size 'n_cell':
//   input_gate_bias_ptr               - optional
//   forget_gate_bias_ptr
//   cell_gate_bias_ptr
//   output_gate_bias_ptr
//
// Layer norm coefficients of size 'n_cell', representing diagonal matrices.
//   input_layer_norm_coefficients_ptr  - optional
//   forget_layer_norm_coefficients_ptr - optional
//   cell_layer_norm_coefficients_ptr   - optional
//   output_layer_norm_coefficients_ptr - optional
//
// Temporary pre-allocated storage for quantized values:
//   quantized_input_ptr (same size as input_ptr)
//   quantized_output_state_ptr (same size as output_state_ptr)
//   quantized_output_scratch (same size as cell_state_ptr)
// Temporary pre-allocated storage for recovered values:
//   recovered_cell_weights (same size as cell_to_*_weights)
//
// Outputs:
//   output_state_ptr - size 'n_batch * n_output'
//   cell_state_ptr   - size 'n_batch * n_cell'
//   output_ptr       - size 'n_batch * output_batch_leading_dim'
inline void LstmStepHybrid(
    const float* input_ptr, const int8_t* input_to_input_weights_ptr,
    const uint8_t* input_to_input_weights_ledger_ptr,
    float input_to_input_weights_scale,
    const int8_t* input_to_forget_weights_ptr,
    const uint8_t* input_to_forget_weights_ledger_ptr,
    float input_to_forget_weights_scale,
    const int8_t* input_to_cell_weights_ptr,
    const uint8_t* input_to_cell_weights_ledger_ptr,
    float input_to_cell_weights_scale,
    const int8_t* input_to_output_weights_ptr,
    const uint8_t* input_to_output_weights_ledger_ptr,
    float input_to_output_weights_scale, const float* aux_input_ptr,
    const int8_t* aux_input_to_input_weights_ptr,
    float aux_input_to_input_weights_scale,
    const int8_t* aux_input_to_forget_weights_ptr,
    float aux_input_to_forget_weights_scale,
    const int8_t* aux_input_to_cell_weights_ptr,
    float aux_input_to_cell_weights_scale,
    const int8_t* aux_input_to_output_weights_ptr,
    float aux_input_to_output_weights_scale,
    const int8_t* recurrent_to_input_weights_ptr,
    const uint8_t* recurrent_to_input_weights_ledger_ptr,
    float recurrent_to_input_weights_scale,
    const int8_t* recurrent_to_forget_weights_ptr,
    const uint8_t* recurrent_to_forget_weights_ledger_ptr,
    float recurrent_to_forget_weights_scale,
    const int8_t* recurrent_to_cell_weights_ptr,
    const uint8_t* recurrent_to_cell_weights_ledger_ptr,
    float recurrent_to_cell_weights_scale,
    const int8_t* recurrent_to_output_weights_ptr,
    const uint8_t* recurrent_to_output_weights_ledger_ptr,
    float recurrent_to_output_weights_scale,
    const int8_t* cell_to_input_weights_ptr, float cell_to_input_weights_scale,
    const int8_t* cell_to_forget_weights_ptr,
    float cell_to_forget_weights_scale,
    const int8_t* cell_to_output_weights_ptr,
    float cell_to_output_weights_scale,
    const float* input_layer_norm_coefficients_ptr,
    const float* forget_layer_norm_coefficients_ptr,
    const float* cell_layer_norm_coefficients_ptr,
    const float* output_layer_norm_coefficients_ptr,
    const float* input_gate_bias_ptr, const float* forget_gate_bias_ptr,
    const float* cell_gate_bias_ptr, const float* output_gate_bias_ptr,
    const int8_t* projection_weights_ptr,
    const uint8_t* projection_weights_ledger_ptr,
    float projection_weights_scale, const float* projection_bias_ptr,
    const TfLiteLSTMParams* params, int n_batch, int n_cell, int n_input,
    int n_aux_input, int n_output, int output_batch_leading_dim,
    float* scratch0, float* scratch1, float* scratch2, float* scratch3,
    float* scales, float* input_sf, float* aux_input_sf, float* output_state_sf,
    float* scaling_factors_scratch, float* recovered_cell_weights,
    int8_t* quantized_input_ptr, int8_t* quantized_aux_input_ptr,
    int8_t* quantized_output_state_ptr, int8_t* quantized_output_scratch,
    float* output_state_ptr, float* cell_state_ptr, int32_t* accum_scratch_ptr,
    float* output_ptr, int32_t* input_zp, int32_t* aux_input_zp,
    int32_t* output_state_zp, int32_t* row_sums, int row_sums_size,
    bool* compute_row_sums, bool asymmetric_quantize_inputs) {
  // Since we have already checked that weights are all there or none, we
  // can check the existence of only one to the get the condition.
  const bool use_cifg = (input_to_input_weights_ptr == nullptr);
  // Make named scratch buffers for the different gates.
  float* input_gate_scratch = scratch0;
  float* forget_gate_scratch = scratch1;
  float* cell_gate_scratch = scratch2;
  float* output_gate_scratch = scratch3;

  int32_t* input_to_input_row_sums = nullptr;
  int32_t* input_to_forget_row_sums = nullptr;
  int32_t* input_to_cell_row_sums = nullptr;
  int32_t* input_to_output_row_sums = nullptr;
  int32_t* aux_input_to_input_row_sums = nullptr;
  int32_t* aux_input_to_forget_row_sums = nullptr;
  int32_t* aux_input_to_cell_row_sums = nullptr;
  int32_t* aux_input_to_output_row_sums = nullptr;
  int32_t* recurrent_to_input_row_sums = nullptr;
  int32_t* recurrent_to_forget_row_sums = nullptr;
  int32_t* recurrent_to_cell_row_sums = nullptr;
  int32_t* recurrent_to_output_row_sums = nullptr;
  int32_t* projection_weights_row_sums = nullptr;

  if (asymmetric_quantize_inputs) {
    int num_row_sums = use_cifg ? 6 : 8;
    if (aux_input_ptr != nullptr) {
      num_row_sums += use_cifg ? 3 : 4;
    }
    if (projection_weights_ptr != nullptr) {
      num_row_sums += ceil(static_cast<float>(n_output) / n_cell);
    }
    TFLITE_DCHECK(row_sums_size == num_row_sums);
    input_to_input_row_sums = row_sums;
    input_to_forget_row_sums =
        use_cifg ? input_to_input_row_sums : input_to_input_row_sums + n_cell;
    input_to_cell_row_sums = input_to_forget_row_sums + n_cell;
    input_to_output_row_sums = input_to_cell_row_sums + n_cell;
    if (aux_input_ptr != nullptr) {
      aux_input_to_input_row_sums = input_to_output_row_sums + n_cell;
      aux_input_to_forget_row_sums = use_cifg
                                         ? aux_input_to_input_row_sums
                                         : aux_input_to_input_row_sums + n_cell;
      aux_input_to_cell_row_sums = aux_input_to_forget_row_sums + n_cell;
      aux_input_to_output_row_sums = aux_input_to_cell_row_sums + n_cell;
    }
    recurrent_to_input_row_sums = aux_input_ptr
                                      ? aux_input_to_output_row_sums + n_cell
                                      : input_to_output_row_sums + n_cell;
    recurrent_to_forget_row_sums = use_cifg
                                       ? recurrent_to_input_row_sums
                                       : recurrent_to_input_row_sums + n_cell;
    recurrent_to_cell_row_sums = recurrent_to_forget_row_sums + n_cell;
    recurrent_to_output_row_sums = recurrent_to_cell_row_sums + n_cell;
    if (projection_weights_ptr != nullptr) {
      projection_weights_row_sums = recurrent_to_output_row_sums + n_cell;
    }
    if (*compute_row_sums) {
      ComputeRowSums(
          input_to_input_row_sums, input_to_forget_row_sums,
          input_to_cell_row_sums, input_to_output_row_sums,
          aux_input_to_input_row_sums, aux_input_to_forget_row_sums,
          aux_input_to_cell_row_sums, aux_input_to_output_row_sums,
          recurrent_to_input_row_sums, recurrent_to_forget_row_sums,
          recurrent_to_cell_row_sums, recurrent_to_output_row_sums,
          projection_weights_row_sums, row_sums, n_cell, n_input, n_aux_input,
          n_output, input_to_input_weights_ptr, input_to_forget_weights_ptr,
          input_to_cell_weights_ptr, input_to_output_weights_ptr,
          aux_input_to_input_weights_ptr, aux_input_to_forget_weights_ptr,
          aux_input_to_cell_weights_ptr, aux_input_to_output_weights_ptr,
          recurrent_to_input_weights_ptr, recurrent_to_forget_weights_ptr,
          recurrent_to_cell_weights_ptr, recurrent_to_output_weights_ptr,
          projection_weights_ptr, use_cifg, aux_input_ptr);
      *compute_row_sums = false;
    }
  }

  // Check if inputs are all zeros so we can skip some computations.
  const bool is_input_all_zeros =
      tflite::tensor_utils::IsZeroVector(input_ptr, n_batch * n_input);
  const bool is_aux_input_all_zeros =
      (aux_input_ptr == nullptr || tflite::tensor_utils::IsZeroVector(
                                       aux_input_ptr, n_batch * n_aux_input));
  const bool is_output_state_all_zeros =
      tflite::tensor_utils::IsZeroVector(output_state_ptr, n_batch * n_output);
  // Quantize inputs.
  if (!is_input_all_zeros) {
    tflite::tensor_utils::BatchQuantizeFloats(
        input_ptr, n_batch, n_input, quantized_input_ptr, input_sf, input_zp,
        asymmetric_quantize_inputs);
  }
  if (!is_aux_input_all_zeros) {
    tflite::tensor_utils::BatchQuantizeFloats(
        aux_input_ptr, n_batch, n_aux_input, quantized_aux_input_ptr,
        aux_input_sf, aux_input_zp, asymmetric_quantize_inputs);
  }
  if (!is_output_state_all_zeros) {
    tflite::tensor_utils::BatchQuantizeFloats(
        output_state_ptr, n_batch, n_output, quantized_output_state_ptr,
        output_state_sf, output_state_zp, asymmetric_quantize_inputs);
  }
  if (!use_cifg) {
    // Calculate the input gate. (If not CIFG.)
    CalculateLstmGateHybrid(
        quantized_input_ptr, input_sf, input_zp, input_to_input_weights_ptr,
        input_to_input_weights_ledger_ptr, input_to_input_weights_scale,
        input_to_input_row_sums, quantized_aux_input_ptr, aux_input_sf,
        aux_input_zp, aux_input_to_input_weights_ptr,
        aux_input_to_input_weights_scale, aux_input_to_input_row_sums,
        quantized_output_state_ptr, output_state_sf, output_state_zp,
        recurrent_to_input_weights_ptr, recurrent_to_input_weights_ledger_ptr,
        recurrent_to_input_weights_scale, recurrent_to_input_row_sums,
        cell_state_ptr, cell_to_input_weights_ptr, cell_to_input_weights_scale,
        input_layer_norm_coefficients_ptr, input_gate_bias_ptr, n_batch,
        n_input, n_aux_input, n_output, n_cell, kTfLiteActSigmoid,
        input_gate_scratch, is_input_all_zeros, is_aux_input_all_zeros,
        is_output_state_all_zeros, compute_row_sums, scaling_factors_scratch,
        recovered_cell_weights, scales, accum_scratch_ptr);
  }
  // Calculate the forget gate.
  CalculateLstmGateHybrid(
      quantized_input_ptr, input_sf, input_zp, input_to_forget_weights_ptr,
      input_to_forget_weights_ledger_ptr, input_to_forget_weights_scale,
      input_to_forget_row_sums, quantized_aux_input_ptr, aux_input_sf,
      aux_input_zp, aux_input_to_forget_weights_ptr,
      aux_input_to_forget_weights_scale, aux_input_to_forget_row_sums,
      quantized_output_state_ptr, output_state_sf, output_state_zp,
      recurrent_to_forget_weights_ptr, recurrent_to_forget_weights_ledger_ptr,
      recurrent_to_forget_weights_scale, recurrent_to_forget_row_sums,
      cell_state_ptr, cell_to_forget_weights_ptr, cell_to_forget_weights_scale,
      forget_layer_norm_coefficients_ptr, forget_gate_bias_ptr, n_batch,
      n_input, n_aux_input, n_output, n_cell, kTfLiteActSigmoid,
      forget_gate_scratch, is_input_all_zeros, is_aux_input_all_zeros,
      is_output_state_all_zeros, compute_row_sums, scaling_factors_scratch,
      recovered_cell_weights, scales, accum_scratch_ptr);
  // Calculate the cell update gate.
  CalculateLstmGateHybrid(
      quantized_input_ptr, input_sf, input_zp, input_to_cell_weights_ptr,
      input_to_cell_weights_ledger_ptr, input_to_cell_weights_scale,
      input_to_cell_row_sums, quantized_aux_input_ptr, aux_input_sf,
      aux_input_zp, aux_input_to_cell_weights_ptr,
      aux_input_to_cell_weights_scale, aux_input_to_cell_row_sums,
      quantized_output_state_ptr, output_state_sf, output_state_zp,
      recurrent_to_cell_weights_ptr, recurrent_to_cell_weights_ledger_ptr,
      recurrent_to_cell_weights_scale, recurrent_to_cell_row_sums,
      /*cell_state=*/nullptr, /*cell_to_gate_weights=*/nullptr,
      /*cell_to_gate_weights_scale=*/0.0f, cell_layer_norm_coefficients_ptr,
      cell_gate_bias_ptr, n_batch, n_input, n_aux_input, n_output, n_cell,
      params->activation, cell_gate_scratch, is_input_all_zeros,
      is_aux_input_all_zeros, is_output_state_all_zeros, compute_row_sums,
      scaling_factors_scratch, recovered_cell_weights, scales,
      accum_scratch_ptr);
  // Update the cell state.
  UpdateLstmCellFloat(n_batch, n_cell, cell_state_ptr, input_gate_scratch,
                      forget_gate_scratch, cell_gate_scratch, use_cifg,
                      params->cell_clip);
  // Calculate the output gate.
  CalculateLstmGateHybrid(
      quantized_input_ptr, input_sf, input_zp, input_to_output_weights_ptr,
      input_to_output_weights_ledger_ptr, input_to_output_weights_scale,
      input_to_output_row_sums, quantized_aux_input_ptr, aux_input_sf,
      aux_input_zp, aux_input_to_output_weights_ptr,
      aux_input_to_output_weights_scale, aux_input_to_output_row_sums,
      quantized_output_state_ptr, output_state_sf, output_state_zp,
      recurrent_to_output_weights_ptr, recurrent_to_output_weights_ledger_ptr,
      recurrent_to_output_weights_scale, recurrent_to_output_row_sums,
      cell_state_ptr, cell_to_output_weights_ptr, cell_to_output_weights_scale,
      output_layer_norm_coefficients_ptr, output_gate_bias_ptr, n_batch,
      n_input, n_aux_input, n_output, n_cell, kTfLiteActSigmoid,
      output_gate_scratch, is_input_all_zeros, is_aux_input_all_zeros,
      is_output_state_all_zeros, compute_row_sums, scaling_factors_scratch,
      recovered_cell_weights, scales, accum_scratch_ptr);
  // Update the output state.
  CalculateLstmOutputHybrid(
      n_batch, n_cell, n_output, cell_state_ptr, output_gate_scratch,
      params->activation, projection_weights_ptr, projection_weights_ledger_ptr,
      projection_weights_scale, projection_bias_ptr, params->proj_clip,
      output_state_ptr, asymmetric_quantize_inputs, projection_weights_row_sums,
      compute_row_sums, scratch2, quantized_output_scratch, input_sf, input_zp,
      accum_scratch_ptr, scales);
  // Copy output state to the output. Note that the output's rows may not be
  // contiguous (output_batch_leading_dim != n_output).
  for (int b = 0; b < n_batch; b++) {
    std::memcpy(output_ptr + b * output_batch_leading_dim,
                output_state_ptr + b * n_output, n_output * sizeof(float));
  }
}

// Fully quantized lstm kernel for 16 bit gate matmul output.
//
// Input tensor of size n_batch * n_input:
//   input_ptr
//
// LSTM weights:
// Quantized input weights of size 'n_cell * n_input':
//   input_to_input_weight_ptr            - optional
//   input_to_forget_weight_ptr           - optional
//   input_to_cell_weight_ptr             - optional
//   input_to_output_weight_ptr           - optional
//
// Quantized recurrent weights of size 'n_cell * n_output':
//   recurrent_to_input_weight_ptr        - optional
//   recurrent_to_forget_weights_ptr
//   recurrent_to_cell_weights_ptr
//   recurrent_to_input_weights_ptr
//
// Quantized peephole weights of size 'n_cell', representing diagonal matrices.
//   cell_to_input_weights               - optional
//   cell_to_cell_weights                - optional
//   cell_to_output_weights              - optional
//
// Quantized projection weights of size 'n_output * n_cell'
//   projection_weight_ptr                     - optional
//
// Weight scales (scalars) for each of the weights above.
//   effective_input_to_input_scale_a    - optional
//   effective_input_to_input_scale_b    - optional
//   effective_input_to_forget_scale_a
//   effective_input_to_forget_scale_b
//   effective_input_to_cell_scale_a
//   effective_input_to_cell_scale_b
//   effective_input_to_output_scale_a
//   effective_input_to_output_scale_b
//   effective_recurrent_to_input_scale_a    - optional
//   effective_recurrent_to_input_scale_b    - optional
//   effective_recurrent_to_forget_scale_a
//   effective_recurrent_to_forget_scale_b
//   effective_recurrent_to_cell_scale_a
//   effective_recurrent_to_cell_scale_b
//   effective_recurrent_to_output_scale_a
//   effective_recurrent_to_output_scale_b
//   effective_proj_scale_a                  - optional
//   effective_proj_scale_b                  - optional
//
// Gate biases of size 'n_cell':
//   input_gate_bias_ptr                 - optional
//   forget_gate_bias_ptr
//   cell_gate_bias_ptr
//   output_gate_bias_ptr
//
// Layer norm coefficients of size 'n_cell', representing diagonal matrices.
//   layer_norm_input_weight_ptr    - optional
//   layer_norm_forget_weight_ptr   - optional
//   layer_norm_cell_weight_ptr     - optional
//   layer_norm_output_weight_ptr   - optional
//
// Layer norm scales of size 'n_cell'.
//   layer_norm_input_scale_a     - optional
//   layer_norm_input_scale_b     - optional
//   layer_norm_forget_scale_a    - optional
//   layer_norm_forget_scale_b    - optional
//   layer_norm_cell_scale_a      - optional
//   layer_norm_cell_scale_b      - optional
//   layer_norm_output_scale_a    - optional
//   layer_norm_output_scale_b    - optional
//
// Scalar values:
//   quantized_cell_clip: quantized clip value for cell.
//   quantized_proj_clip: quantized clip value for projection.
//   cell_state_scale: the power of two scale for cell state.
//
// Zero points:
//   output_state_zp: zero point of output state
//   hidden_zp: zero point for hidden state.
//
// Temporary pre-allocated storage for the calculation. Each is of size n_cell *
// n_batch.
//   scratch0
//   scratch1
//   scratch2
//   scratch3
//   scratch4
//   scratch5: this scratch buffer is created purely for optimizing the
//              MatrixBatchVectorMultiplyAccumulate.
//
// Outputs:
//   output_state_ptr - size 'n_batch * n_output'
//   cell_state_ptr   - size 'n_batch * n_cell'
//   output_ptr       - size 'n_batch * n_output'
// TODO(b/159947023): scratch0 is not used if (!cifg). Don't allocate then.
inline void LstmStepInteger8x8_16(
    const int8_t* input_ptr, const int8_t* input_to_input_weight_ptr,
    int32_t effective_input_to_input_scale_a,
    int32_t effective_input_to_input_scale_b,
    const int8_t* input_to_forget_weight_ptr,
    int32_t effective_input_to_forget_scale_a,
    int32_t effective_input_to_forget_scale_b,
    const int8_t* input_to_cell_weight_ptr,
    int32_t effective_input_to_cell_scale_a,
    int32_t effective_input_to_cell_scale_b,
    const int8_t* input_to_output_weight_ptr,
    int32_t effective_input_to_output_scale_a,
    int32_t effective_input_to_output_scale_b,
    const int8_t* recurrent_to_input_weight_ptr,
    int32_t effective_recurrent_to_input_scale_a,
    int32_t effective_recurrent_to_input_scale_b,
    const int8_t* recurrent_to_forget_weight_ptr,
    int32_t effective_recurrent_to_forget_scale_a,
    int32_t effective_recurrent_to_forget_scale_b,
    const int8_t* recurrent_to_cell_weight_ptr,
    int32_t effective_recurrent_to_cell_scale_a,
    int32_t effective_recurrent_to_cell_scale_b,
    const int8_t* recurrent_to_output_weight_ptr,
    int32_t effective_recurrent_to_output_scale_a,
    int32_t effective_recurrent_to_output_scale_b,
    const int16_t* cell_to_input_weight_ptr,
    int32_t effective_cell_to_input_scale_a,
    int32_t effective_cell_to_input_scale_b,
    const int16_t* cell_to_forget_weight_ptr,
    int32_t effective_cell_to_forget_scale_a,
    int32_t effective_cell_to_forget_scale_b,
    const int16_t* cell_to_output_weight_ptr,
    int32_t effective_cell_to_output_scale_a,
    int32_t effective_cell_to_output_scale_b,
    const int8_t* projection_weight_ptr, int32_t effective_proj_scale_a,
    int32_t effective_proj_scale_b, int32_t hidden_zp,
    int32_t effective_hidden_scale_a, int32_t effective_hidden_scale_b,
    const int16_t* layer_norm_input_weight_ptr,
    int32_t layer_norm_input_scale_a, int32_t layer_norm_input_scale_b,
    const int16_t* layer_norm_forget_weight_ptr,
    int32_t layer_norm_forget_scale_a, int32_t layer_norm_forget_scale_b,
    const int16_t* layer_norm_cell_weight_ptr, int32_t layer_norm_cell_scale_a,
    int32_t layer_norm_cell_scale_b,
    const int16_t* layer_norm_output_weight_ptr,
    int32_t layer_norm_output_scale_a, int32_t layer_norm_output_scale_b,
    const int32_t* input_gate_bias_ptr, const int32_t* forget_gate_bias_ptr,
    const int32_t* cell_gate_bias_ptr, const int32_t* output_gate_bias_ptr,
    int16_t quantized_cell_clip, int8_t quantized_proj_clip,
    int32_t cell_state_scale, int32_t input_variance_guard,
    int32_t forget_variance_guard, int32_t cell_variance_guard,
    int32_t output_variance_guard,
    const int32_t* input_to_forget_effective_bias,
    const int32_t* recurrent_to_forget_effective_bias,
    const int32_t* input_to_cell_effective_bias,
    const int32_t* recurrent_to_cell_effective_bias,
    const int32_t* input_to_output_effective_bias,
    const int32_t* recurrent_to_output_effective_bias,
    const int32_t* input_to_input_effective_bias,
    const int32_t* recurrent_to_input_effective_bias,
    const int32_t* projection_effective_bias, int n_batch, int n_cell,
    int n_input, int n_output, int8_t* output_state_ptr,
    int32_t output_state_zp, int16_t* cell_state_ptr, int8_t* output_ptr,
    int16_t* scratch0, int16_t* scratch1, int16_t* scratch2, int16_t* scratch3,
    int8_t* scratch4, int32_t* scratch5) {
  // Make named scratch buffers for the different gates.
  int16_t* input_gate_scratch = scratch0;
  int16_t* forget_gate_scratch = scratch1;
  int16_t* cell_gate_scratch = scratch2;
  int16_t* output_gate_scratch = scratch3;

  // Since we have already checked that weights are all there or none, we
  // can check the existence of only one to the get the condition.
  const bool use_cifg = (input_to_input_weight_ptr == nullptr);

  // Check for nullptrs.
  TFLITE_DCHECK(input_to_forget_effective_bias);
  TFLITE_DCHECK(recurrent_to_forget_effective_bias);
  TFLITE_DCHECK(input_to_cell_effective_bias);
  TFLITE_DCHECK(recurrent_to_cell_effective_bias);
  TFLITE_DCHECK(input_to_output_effective_bias);
  TFLITE_DCHECK(recurrent_to_output_effective_bias);
  if (!use_cifg) {
    TFLITE_DCHECK(input_to_input_effective_bias);
    TFLITE_DCHECK(recurrent_to_input_effective_bias);
  }
  const bool use_projection = (projection_weight_ptr != nullptr);
  if (use_projection) {
    TFLITE_DCHECK(projection_effective_bias);
  }
  if (!use_cifg) {
    // Calculate the input gate. (If not CIFG.)
    CalculateLstmGateInteger8x8_16(
        input_ptr, input_to_input_weight_ptr, input_to_input_effective_bias,
        effective_input_to_input_scale_a, effective_input_to_input_scale_b,
        output_state_ptr, recurrent_to_input_weight_ptr,
        recurrent_to_input_effective_bias, effective_recurrent_to_input_scale_a,
        effective_recurrent_to_input_scale_b, cell_state_ptr,
        cell_to_input_weight_ptr, effective_cell_to_input_scale_a,
        effective_cell_to_input_scale_b, layer_norm_input_weight_ptr,
        input_gate_bias_ptr, layer_norm_input_scale_a, layer_norm_input_scale_b,
        input_variance_guard, n_batch, n_input, n_output, n_cell,
        kTfLiteActSigmoid, input_gate_scratch, scratch5);
  }
  // Calculate the forget gate.
  CalculateLstmGateInteger8x8_16(
      input_ptr, input_to_forget_weight_ptr, input_to_forget_effective_bias,
      effective_input_to_forget_scale_a, effective_input_to_forget_scale_b,
      output_state_ptr, recurrent_to_forget_weight_ptr,
      recurrent_to_forget_effective_bias, effective_recurrent_to_forget_scale_a,
      effective_recurrent_to_forget_scale_b, cell_state_ptr,
      cell_to_forget_weight_ptr, effective_cell_to_forget_scale_a,
      effective_cell_to_forget_scale_b, layer_norm_forget_weight_ptr,
      forget_gate_bias_ptr, layer_norm_forget_scale_a,
      layer_norm_forget_scale_b, forget_variance_guard, n_batch, n_input,
      n_output, n_cell, kTfLiteActSigmoid, forget_gate_scratch, scratch5);
  // Calculate the cell update gate.
  CalculateLstmGateInteger8x8_16(
      input_ptr, input_to_cell_weight_ptr, input_to_cell_effective_bias,
      effective_input_to_cell_scale_a, effective_input_to_cell_scale_b,
      output_state_ptr, recurrent_to_cell_weight_ptr,
      recurrent_to_cell_effective_bias, effective_recurrent_to_cell_scale_a,
      effective_recurrent_to_cell_scale_b, cell_state_ptr,
      /*cell_to_gate_weights=*/nullptr, /*cell_to_gate_scale_a=*/0,
      /*cell_to_gate_scale_b=*/0, layer_norm_cell_weight_ptr,
      cell_gate_bias_ptr, layer_norm_cell_scale_a, layer_norm_cell_scale_b,
      cell_variance_guard, n_batch, n_input, n_output, n_cell, kTfLiteActTanh,
      cell_gate_scratch, scratch5);
  // Update the cell state.
  UpdateLstmCellInteger(n_batch, n_cell, cell_state_ptr, cell_state_scale,
                        input_gate_scratch, forget_gate_scratch,
                        cell_gate_scratch, use_cifg, quantized_cell_clip);
  // Calculate the output gate.
  CalculateLstmGateInteger8x8_16(
      input_ptr, input_to_output_weight_ptr, input_to_output_effective_bias,
      effective_input_to_output_scale_a, effective_input_to_output_scale_b,
      output_state_ptr, recurrent_to_output_weight_ptr,
      recurrent_to_output_effective_bias, effective_recurrent_to_output_scale_a,
      effective_recurrent_to_output_scale_b, cell_state_ptr,
      cell_to_output_weight_ptr, effective_cell_to_output_scale_a,
      effective_cell_to_output_scale_b, layer_norm_output_weight_ptr,
      output_gate_bias_ptr, layer_norm_output_scale_a,
      layer_norm_output_scale_b, output_variance_guard, n_batch, n_input,
      n_output, n_cell, kTfLiteActSigmoid, output_gate_scratch, scratch5);
  // Update the output state.
  CalculateLstmOutputInteger8x8_16(
      n_batch, n_cell, n_output, cell_state_ptr, cell_state_scale,
      output_gate_scratch, effective_hidden_scale_a, effective_hidden_scale_b,
      hidden_zp, projection_weight_ptr, effective_proj_scale_a,
      effective_proj_scale_b, projection_effective_bias, output_state_zp,
      quantized_proj_clip, output_state_ptr, scratch0, scratch4, scratch5);
  // Copy output state to the output. Note that unlike float or hybrid, output
  // is always contiguous.
  std::memcpy(output_ptr, output_state_ptr,
              n_batch * n_output * sizeof(int8_t));
}

// Fully quantized lstm kernel for 8 bit gate matmul output.
//
// Input tensor of size n_batch * n_input:
//   input_ptr
//
// LSTM weights:
// Quantized input weights of size 'n_cell * n_input':
//   input_to_input_weight_ptr            - optional
//   input_to_forget_weight_ptr           - optional
//   input_to_cell_weight_ptr             - optional
//   input_to_output_weight_ptr           - optional
//
// Quantized recurrent weights of size 'n_cell * n_output':
//   recurrent_to_input_weight_ptr        - optional
//   recurrent_to_forget_weights_ptr
//   recurrent_to_cell_weights_ptr
//   recurrent_to_input_weights_ptr
//
// Quantized peephole weights of size 'n_cell', representing diagonal matrices.
//   cell_to_input_weights               - optional
//   cell_to_cell_weights                - optional
//   cell_to_output_weights              - optional
//
// Quantized projection weights of size 'n_output * n_cell'
//   projection_weight_ptr                     - optional
//
// Weight scales (scalars) for each of the weights above.
//   effective_input_to_input_scale_a    - optional
//   effective_input_to_input_scale_b    - optional
//   effective_input_to_forget_scale_a
//   effective_input_to_forget_scale_b
//   effective_input_to_cell_scale_a
//   effective_input_to_cell_scale_b
//   effective_input_to_output_scale_a
//   effective_input_to_output_scale_b
//   effective_recurrent_to_input_scale_a    - optional
//   effective_recurrent_to_input_scale_b    - optional
//   effective_recurrent_to_forget_scale_a
//   effective_recurrent_to_forget_scale_b
//   effective_recurrent_to_cell_scale_a
//   effective_recurrent_to_cell_scale_b
//   effective_recurrent_to_output_scale_a
//   effective_recurrent_to_output_scale_b
//   effective_proj_scale_a                  - optional
//   effective_proj_scale_b                  - optional
//
// Gate biases of size 'n_cell':
//   input_gate_bias_ptr                 - optional
//   forget_gate_bias_ptr
//   cell_gate_bias_ptr
//   output_gate_bias_ptr
//
// Layer norm coefficients of size 'n_cell', representing diagonal matrices.
//   layer_norm_input_weight_ptr    - optional
//   layer_norm_forget_weight_ptr   - optional
//   layer_norm_cell_weight_ptr     - optional
//   layer_norm_output_weight_ptr   - optional
//
// Layer norm scales of size 'n_cell'.
//   layer_norm_input_scale_a     - optional
//   layer_norm_input_scale_b     - optional
//   layer_norm_forget_scale_a    - optional
//   layer_norm_forget_scale_b    - optional
//   layer_norm_cell_scale_a      - optional
//   layer_norm_cell_scale_b      - optional
//   layer_norm_output_scale_a    - optional
//   layer_norm_output_scale_b    - optional
//
// Scalar values:
//   quantized_cell_clip: quantized clip value for cell.
//   quantized_proj_clip: quantized clip value for projection.
//   cell_state_scale: the power of two scale for cell state.
//
// Zero points:
//   input_zp: zero point for input tensor.
//   output_state_zp: zero point of output state.
//   hidden_zp: zero point for hidden state.
//
// Temporary pre-allocated storage for the calculation. Each is of size n_cell *
// n_batch.
//   scratch0
//   scratch1
//   scratch2
//   scratch3
//   scratch4
//   scratch5
//   scratch6
//   scratch7
//
// Outputs:
//   output_state_ptr - size 'n_batch * n_output'
//   cell_state_ptr   - size 'n_batch * n_cell'
//   output_ptr       - size 'n_batch * n_output'
//
// Can move zero point calculation into Prepare() for better perfomance.
// TODO(b/159947023): scratch5 is unused, remove.
inline void LstmStepInteger8x8_8(
    const int8_t* input_ptr, int32_t input_zp,
    const int8_t* input_to_input_weight_ptr,
    int32_t effective_input_to_input_scale_a,
    int32_t effective_input_to_input_scale_b,
    const int8_t* input_to_forget_weight_ptr,
    int32_t effective_input_to_forget_scale_a,
    int32_t effective_input_to_forget_scale_b,
    const int8_t* input_to_cell_weight_ptr,
    int32_t effective_input_to_cell_scale_a,
    int32_t effective_input_to_cell_scale_b,
    const int8_t* input_to_output_weight_ptr,
    int32_t effective_input_to_output_scale_a,
    int32_t effective_input_to_output_scale_b,
    const int8_t* recurrent_to_input_weight_ptr,
    int32_t effective_recurrent_to_input_scale_a,
    int32_t effective_recurrent_to_input_scale_b,
    const int8_t* recurrent_to_forget_weight_ptr,
    int32_t effective_recurrent_to_forget_scale_a,
    int32_t effective_recurrent_to_forget_scale_b,
    const int8_t* recurrent_to_cell_weight_ptr,
    int32_t effective_recurrent_to_cell_scale_a,
    int32_t effective_recurrent_to_cell_scale_b,
    const int8_t* recurrent_to_output_weight_ptr,
    int32_t effective_recurrent_to_output_scale_a,
    int32_t effective_recurrent_to_output_scale_b,
    const int8_t* cell_to_input_weight_ptr,
    int32_t effective_cell_to_input_scale_a,
    int32_t effective_cell_to_input_scale_b,
    const int8_t* cell_to_forget_weight_ptr,
    int32_t effective_cell_to_forget_scale_a,
    int32_t effective_cell_to_forget_scale_b,
    const int8_t* cell_to_output_weight_ptr,
    int32_t effective_cell_to_output_scale_a,
    int32_t effective_cell_to_output_scale_b,
    const int8_t* projection_weight_ptr, int32_t effective_proj_scale_a,
    int32_t effective_proj_scale_b, const int16_t* layer_norm_input_weight_ptr,
    int32_t layer_norm_input_scale_a, int32_t layer_norm_input_scale_b,
    const int16_t* layer_norm_forget_weight_ptr,
    int32_t layer_norm_forget_scale_a, int32_t layer_norm_forget_scale_b,
    const int16_t* layer_norm_cell_weight_ptr, int32_t layer_norm_cell_scale_a,
    int32_t layer_norm_cell_scale_b,
    const int16_t* layer_norm_output_weight_ptr,
    int32_t layer_norm_output_scale_a, int32_t layer_norm_output_scale_b,
    const int32_t* input_gate_bias_ptr, const int32_t* forget_gate_bias_ptr,
    const int32_t* cell_gate_bias_ptr, const int32_t* output_gate_bias_ptr,
    const int32_t* projection_bias_ptr, const TfLiteLSTMParams* params,
    const int32_t* intermediate_scale_a, const int32_t* intermediate_scale_b,
    const int32_t* intermediate_zp, int16_t quantized_cell_clip,
    int8_t quantized_proj_clip, int n_batch, int n_cell, int n_input,
    int n_output, int output_batch_leading_dim, int8_t* output_state_ptr,
    int32_t output_state_zp, int16_t* cell_state_ptr, int8_t* output_ptr,
    int8_t* scratch0, int8_t* scratch1, int16_t* scratch2, int16_t* scratch3,
    int16_t* scratch4, int16_t* scratch5, int16_t* scratch6,
    int16_t* scratch7) {
  // TODO(b/159066113): scratch5 is unused, remove.

  // Make named scratch buffers for the different gates.
  int16_t* forget_gate_scratch = scratch2;
  int16_t* cell_gate_scratch = scratch3;
  int16_t* output_gate_scratch = scratch4;
  // no-CIFG is not supported here

  // Calculate the forget gate.
  CalculateLstmGateInteger8x8_8(
      input_ptr, input_zp, input_to_forget_weight_ptr,
      effective_input_to_forget_scale_a, effective_input_to_forget_scale_b,
      intermediate_scale_a[2], intermediate_scale_b[2], intermediate_zp[4],
      output_state_ptr, output_state_zp, recurrent_to_forget_weight_ptr,
      effective_recurrent_to_forget_scale_a,
      effective_recurrent_to_forget_scale_b, intermediate_scale_a[3],
      intermediate_scale_b[3], intermediate_zp[5], layer_norm_forget_weight_ptr,
      layer_norm_forget_scale_a, layer_norm_forget_scale_b,
      forget_gate_bias_ptr, n_batch, n_input, n_output, n_cell,
      kTfLiteActSigmoid, forget_gate_scratch, scratch0, scratch1);
  // Calculate the cell update gate.
  CalculateLstmGateInteger8x8_8(
      input_ptr, input_zp, input_to_cell_weight_ptr,
      effective_input_to_cell_scale_a, effective_input_to_cell_scale_b,
      intermediate_scale_a[4], intermediate_scale_b[4], intermediate_zp[7],
      output_state_ptr, output_state_zp, recurrent_to_cell_weight_ptr,
      effective_recurrent_to_cell_scale_a, effective_recurrent_to_cell_scale_b,
      intermediate_scale_a[5], intermediate_scale_b[5], intermediate_zp[8],
      layer_norm_cell_weight_ptr, layer_norm_cell_scale_a,
      layer_norm_cell_scale_b, cell_gate_bias_ptr, n_batch, n_input, n_output,
      n_cell, kTfLiteActTanh, cell_gate_scratch, scratch0, scratch1);
  // Update the cell state.
  UpdateLstmCellInteger(n_batch, n_cell, cell_state_ptr,
                        /*cell_state_scale=*/-15, /*input_gate=*/nullptr,
                        forget_gate_scratch, cell_gate_scratch,
                        /*use_cifg=*/true, quantized_cell_clip);
  // Calculate the output gate.
  CalculateLstmGateInteger8x8_8(
      input_ptr, input_zp, input_to_output_weight_ptr,
      effective_input_to_output_scale_a, effective_input_to_output_scale_b,
      intermediate_scale_a[6], intermediate_scale_b[6], intermediate_zp[10],
      output_state_ptr, output_state_zp, recurrent_to_output_weight_ptr,
      effective_recurrent_to_output_scale_a,
      effective_recurrent_to_output_scale_b, intermediate_scale_a[11],
      intermediate_scale_b[7], intermediate_zp[7], layer_norm_output_weight_ptr,
      layer_norm_output_scale_a, layer_norm_output_scale_b,
      output_gate_bias_ptr, n_batch, n_input, n_output, n_cell,
      kTfLiteActSigmoid, output_gate_scratch, scratch0, scratch1);
  // Update the output state.
  CalculateLstmOutputInteger8x8_8(
      n_batch, n_cell, n_output, cell_state_ptr, output_gate_scratch,
      projection_weight_ptr, effective_proj_scale_a, effective_proj_scale_b,
      projection_bias_ptr, output_state_zp, quantized_proj_clip,
      output_state_ptr, scratch2);
  // Copy output state to the output. Note that unlike float or hybrid, output
  // is always contigous.
  std::memcpy(output_ptr, output_state_ptr,
              n_batch * n_output * sizeof(int8_t));
}

}  // namespace

TfLiteStatus EvalFloatLstm(
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
    const TfLiteEvalTensor* projection_bias, const TfLiteLSTMParams* params,
    bool forward_sequence, bool time_major, int output_offset,
    float* scratch_buffer, TfLiteEvalTensor* output_state,
    TfLiteEvalTensor* cell_state, TfLiteEvalTensor* output) {
  TFLITE_DCHECK(input->dims->size >= 2 && input->dims->size <= 3);
  int max_time, n_batch;
  if (input->dims->size == 3) {
    max_time = (time_major) ? input->dims->data[0] : input->dims->data[1];
    n_batch = (time_major) ? input->dims->data[1] : input->dims->data[0];
  } else {
    max_time = 1;
    n_batch = input->dims->data[0];
  }
  const int n_input = input->dims->data[input->dims->size - 1];
  const int aux_input_size =
      (aux_input) ? aux_input->dims->data[aux_input->dims->size - 1] : 0;

  // n_cell and n_output will be the same size when there is no projection.
  const int n_cell = input_to_output_weights->dims->data[0];
  const int n_output = recurrent_to_output_weights->dims->data[1];

  // Since we have already checked that weights are all there or none, we can
  // check the existence of only one to the get the condition.
  const bool use_cifg = (input_to_input_weights == nullptr);

  // Index the scratch buffers pointers to the global scratch buffer.
  float* input_gate_scratch = nullptr;
  float* cell_gate_scratch = nullptr;
  float* forget_gate_scratch = nullptr;
  float* output_gate_scratch = nullptr;
  if (use_cifg) {
    cell_gate_scratch = scratch_buffer;
    forget_gate_scratch = scratch_buffer + n_cell * n_batch;
    output_gate_scratch = scratch_buffer + 2 * n_cell * n_batch;
  } else {
    input_gate_scratch = scratch_buffer;
    cell_gate_scratch = scratch_buffer + n_cell * n_batch;
    forget_gate_scratch = scratch_buffer + 2 * n_cell * n_batch;
    output_gate_scratch = scratch_buffer + 3 * n_cell * n_batch;
  }

  const int output_batch_leading_dim =
      output->dims->data[output->dims->size - 1];
  if (time_major) {
    // Loop through the sequence.
    const int input_step = n_batch * n_input;
    const int output_step = n_batch * output_batch_leading_dim;
    for (int t = 0; t < max_time; t++) {
      // If this is the forward_sequence, step forward, otherwise step
      // backwards.
      const int t_rel = forward_sequence ? t : max_time - t - 1;
      const float* input_ptr =
          tflite::micro::GetTensorData<float>(input) + t_rel * input_step;
      const float* aux_input_ptr = nullptr;
      if (aux_input) {
        aux_input_ptr =
            tflite::micro::GetTensorData<float>(aux_input) + t_rel * input_step;
      }
      float* output_ptr = tflite::micro::GetTensorData<float>(output) +
                          t_rel * output_step + output_offset;

      LstmStepFloat(
          input_ptr,
          input_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_to_input_weights),
          input_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_to_forget_weights),
          input_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_to_cell_weights),
          input_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_to_output_weights),
          aux_input_ptr,
          aux_input_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(aux_input_to_input_weights),
          aux_input_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    aux_input_to_forget_weights),
          aux_input_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(aux_input_to_cell_weights),
          aux_input_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    aux_input_to_output_weights),
          recurrent_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(recurrent_to_input_weights),
          recurrent_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    recurrent_to_forget_weights),
          recurrent_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(recurrent_to_cell_weights),
          recurrent_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    recurrent_to_output_weights),
          cell_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(cell_to_input_weights),
          cell_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(cell_to_forget_weights),
          cell_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(cell_to_output_weights),
          input_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    input_layer_norm_coefficients),
          forget_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    forget_layer_norm_coefficients),
          cell_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    cell_layer_norm_coefficients),
          output_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    output_layer_norm_coefficients),
          input_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_gate_bias),
          forget_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(forget_gate_bias),
          cell_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(cell_gate_bias),
          output_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(output_gate_bias),
          projection_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(projection_weights),
          projection_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(projection_bias),
          params, n_batch, n_cell, n_input, aux_input_size, n_output,
          output_batch_leading_dim,
          tflite::micro::GetTensorData<float>(output_state),
          tflite::micro::GetTensorData<float>(cell_state), input_gate_scratch,
          forget_gate_scratch, cell_gate_scratch, output_gate_scratch,
          output_ptr);
    }
  } else {
    for (int b = 0; b < n_batch; b++) {
      const int input_step = n_input;
      const int output_step = output_batch_leading_dim;
      for (int t = 0; t < max_time; t++) {
        // If this is the forward_sequence, step forward, otherwise step
        // backwards.
        const int t_rel = forward_sequence ? t : max_time - t - 1;
        const int time_offset = b * max_time + t_rel;
        const float* input_ptr = tflite::micro::GetTensorData<float>(input) +
                                 time_offset * input_step;
        const float* aux_input_ptr = nullptr;
        if (aux_input) {
          aux_input_ptr = tflite::micro::GetTensorData<float>(aux_input) +
                          time_offset * input_step;
        }
        float* output_ptr = tflite::micro::GetTensorData<float>(output) +
                            time_offset * output_step + output_offset;

        // Offset the {output,cell}_state pointers to the right batch.
        float* output_state_ptr =
            tflite::micro::GetTensorData<float>(output_state) +
            b * output_batch_leading_dim;
        float* cell_state_ptr =
            tflite::micro::GetTensorData<float>(cell_state) + b * n_cell;
        // Offset the scratch pointers to the right batch.
        float* input_gate_scratch_ptr =
            input_gate_scratch ? input_gate_scratch + b * n_cell : nullptr;
        float* forget_gate_scratch_ptr = forget_gate_scratch + b * n_cell;
        float* cell_gate_scratch_ptr = cell_gate_scratch + b * n_cell;
        float* output_gate_scratch_ptr = output_gate_scratch + b * n_cell;

        LstmStepFloat(
            input_ptr,
            input_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_to_input_weights),
            input_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_to_forget_weights),
            input_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_to_cell_weights),
            input_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_to_output_weights),
            aux_input_ptr,
            aux_input_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      aux_input_to_input_weights),
            aux_input_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      aux_input_to_forget_weights),
            aux_input_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      aux_input_to_cell_weights),
            aux_input_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      aux_input_to_output_weights),
            recurrent_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      recurrent_to_input_weights),
            recurrent_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      recurrent_to_forget_weights),
            recurrent_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      recurrent_to_cell_weights),
            recurrent_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      recurrent_to_output_weights),
            cell_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(cell_to_input_weights),
            cell_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(cell_to_forget_weights),
            cell_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(cell_to_output_weights),
            input_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      input_layer_norm_coefficients),
            forget_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      forget_layer_norm_coefficients),
            cell_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      cell_layer_norm_coefficients),
            output_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      output_layer_norm_coefficients),
            input_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_gate_bias),
            forget_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(forget_gate_bias),
            cell_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(cell_gate_bias),
            output_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(output_gate_bias),
            projection_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(projection_weights),
            projection_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(projection_bias),
            params,
            /*n_batch=*/1, n_cell, n_input, aux_input_size, n_output,
            output_batch_leading_dim, output_state_ptr, cell_state_ptr,
            input_gate_scratch_ptr, forget_gate_scratch_ptr,
            cell_gate_scratch_ptr, output_gate_scratch_ptr, output_ptr);
      }
    }
  }
  return kTfLiteOk;
}

TfLiteStatus EvalHybridLstm(
    const HybridLstmScales* hybrid_lstm_scales, const TfLiteEvalTensor* input,
    const TfLiteEvalTensor* input_to_input_weights,
    const TfLiteEvalTensor* input_to_input_weights_ledger,
    const TfLiteEvalTensor* input_to_forget_weights,
    const TfLiteEvalTensor* input_to_forget_weights_ledger,
    const TfLiteEvalTensor* input_to_cell_weights,
    const TfLiteEvalTensor* input_to_cell_weights_ledger,
    const TfLiteEvalTensor* input_to_output_weights,
    const TfLiteEvalTensor* input_to_output_weights_ledger,
    const TfLiteEvalTensor* recurrent_to_input_weights,
    const TfLiteEvalTensor* recurrent_to_input_weights_ledger,
    const TfLiteEvalTensor* recurrent_to_forget_weights,
    const TfLiteEvalTensor* recurrent_to_forget_weights_ledger,
    const TfLiteEvalTensor* recurrent_to_cell_weights,
    const TfLiteEvalTensor* recurrent_to_cell_weights_ledger,
    const TfLiteEvalTensor* recurrent_to_output_weights,
    const TfLiteEvalTensor* recurrent_to_output_weights_ledger,
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
    const TfLiteEvalTensor* projection_weights_ledger,
    const TfLiteEvalTensor* projection_bias, const TfLiteLSTMParams* params,
    bool forward_sequence, bool time_major, int output_offset,
    float* scratch_buffer, float* input_sf, float* aux_input_sf,
    float* output_state_sf, float* prod_scaling_factors,
    float* recovered_cell_weights, int8_t* input_quantized,
    int8_t* aux_input_quantized, int8_t* output_state_quantized,
    int8_t* cell_state_quantized, float* scales, TfLiteEvalTensor* output_state,
    TfLiteEvalTensor* cell_state, int32_t* output_scratch_buffer,
    TfLiteEvalTensor* output, int32_t* input_zp, int32_t* aux_input_zp,
    int32_t* output_state_zp, int32_t* row_sums, int row_sums_size,
    bool* compute_row_sums) {
  TFLITE_DCHECK(input->dims->size >= 2 && input->dims->size <= 3);
  const int n_input = input->dims->data[input->dims->size - 1];
  int max_time, n_batch;
  if (input->dims->size == 2) {
    max_time = 1;
    n_batch = input->dims->data[0];
  } else {
    max_time = (time_major) ? input->dims->data[0] : input->dims->data[1];
    n_batch = (time_major) ? input->dims->data[1] : input->dims->data[0];
  }
  const int aux_input_size =
      (aux_input) ? aux_input->dims->data[aux_input->dims->size - 1] : 0;
  // n_cell and n_output will be the same size when there is no projection.
  const int n_cell = input_to_output_weights->dims->data[0];
  const int n_output = recurrent_to_output_weights->dims->data[1];

  // Since we have already checked that weights are all there or none, we can
  // check the existence of only one to get the condition.
  const bool use_cifg = (input_to_input_weights == nullptr);

  float* input_gate_scratch = nullptr;
  float* cell_gate_scratch = nullptr;
  float* forget_gate_scratch = nullptr;
  float* output_gate_scratch = nullptr;
  if (use_cifg) {
    cell_gate_scratch = scratch_buffer;
    forget_gate_scratch = scratch_buffer + n_cell * n_batch;
    output_gate_scratch = scratch_buffer + 2 * n_cell * n_batch;
  } else {
    input_gate_scratch = scratch_buffer;
    cell_gate_scratch = scratch_buffer + n_cell * n_batch;
    forget_gate_scratch = scratch_buffer + 2 * n_cell * n_batch;
    output_gate_scratch = scratch_buffer + 3 * n_cell * n_batch;
  }

  const int output_batch_leading_dim =
      output->dims->data[output->dims->size - 1];

  int32_t* input_zp_ptr = nullptr;
  int32_t* aux_input_zp_ptr = nullptr;
  int32_t* output_state_zp_ptr = nullptr;
  int32_t* row_sums_ptr = nullptr;
  if (params->asymmetric_quantize_inputs) {
    input_zp_ptr = input_zp;
    aux_input_zp_ptr = aux_input_zp;
    output_state_zp_ptr = output_state_zp;
    row_sums_ptr = row_sums;
  }

  if (time_major) {
    // Feed the sequence into the LSTM step-by-step.
    const int input_step = n_batch * n_input;
    const int output_step = n_batch * output_batch_leading_dim;
    for (int t = 0; t < max_time; t++) {
      // If this is the forward_sequence, step forward, otherwise step
      // backwards.
      const int t_rel = forward_sequence ? t : max_time - t - 1;
      const float* input_ptr =
          tflite::micro::GetTensorData<float>(input) + t_rel * input_step;
      const float* aux_input_ptr = nullptr;
      if (aux_input) {
        aux_input_ptr =
            tflite::micro::GetTensorData<float>(aux_input) + t_rel * input_step;
      }
      float* output_ptr = tflite::micro::GetTensorData<float>(output) +
                          t_rel * output_step + output_offset;
      LstmStepHybrid(
          input_ptr,
          input_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_input_weights),
          input_to_input_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    input_to_input_weights_ledger),
          hybrid_lstm_scales->input_to_input_weights_scale,
          input_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_forget_weights),
          input_to_forget_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    input_to_forget_weights_ledger),
          hybrid_lstm_scales->input_to_forget_weights_scale,
          input_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_cell_weights),
          input_to_cell_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    input_to_cell_weights_ledger),
          hybrid_lstm_scales->input_to_cell_weights_scale,
          input_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_output_weights),
          input_to_output_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    input_to_output_weights_ledger),
          hybrid_lstm_scales->input_to_output_weights_scale, aux_input_ptr,
          aux_input_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    aux_input_to_input_weights),
          hybrid_lstm_scales->aux_input_to_input_weights_scale,
          aux_input_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    aux_input_to_forget_weights),
          hybrid_lstm_scales->aux_input_to_forget_weights_scale,
          aux_input_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(aux_input_to_cell_weights),
          hybrid_lstm_scales->aux_input_to_cell_weights_scale,
          aux_input_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    aux_input_to_output_weights),
          hybrid_lstm_scales->aux_input_to_output_weights_scale,
          recurrent_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_input_weights),
          recurrent_to_input_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    recurrent_to_input_weights_ledger),
          hybrid_lstm_scales->recurrent_to_input_weights_scale,
          recurrent_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_forget_weights),
          recurrent_to_forget_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    recurrent_to_forget_weights_ledger),
          hybrid_lstm_scales->recurrent_to_forget_weights_scale,
          recurrent_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(recurrent_to_cell_weights),
          recurrent_to_cell_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    recurrent_to_cell_weights_ledger),
          hybrid_lstm_scales->recurrent_to_cell_weights_scale,
          recurrent_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_output_weights),
          recurrent_to_output_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    recurrent_to_output_weights_ledger),
          hybrid_lstm_scales->recurrent_to_output_weights_scale,
          cell_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(cell_to_input_weights),
          hybrid_lstm_scales->cell_to_input_weights_scale,
          cell_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(cell_to_forget_weights),
          hybrid_lstm_scales->cell_to_forget_weights_scale,
          cell_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(cell_to_output_weights),
          hybrid_lstm_scales->cell_to_output_weights_scale,
          input_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    input_layer_norm_coefficients),
          forget_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    forget_layer_norm_coefficients),
          cell_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    cell_layer_norm_coefficients),
          output_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(
                    output_layer_norm_coefficients),
          input_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(input_gate_bias),
          forget_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(forget_gate_bias),
          cell_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(cell_gate_bias),
          output_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(output_gate_bias),
          projection_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(projection_weights),
          projection_weights_ledger == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<uint8_t>(
                    projection_weights_ledger),
          hybrid_lstm_scales->projection_weights_scale,
          projection_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<float>(projection_bias),
          params, n_batch, n_cell, n_input, aux_input_size, n_output,
          output_batch_leading_dim, input_gate_scratch, forget_gate_scratch,
          cell_gate_scratch, output_gate_scratch, scales, input_sf,
          aux_input_sf, output_state_sf, prod_scaling_factors,
          recovered_cell_weights, input_quantized, aux_input_quantized,
          output_state_quantized, cell_state_quantized,
          tflite::micro::GetTensorData<float>(output_state),
          tflite::micro::GetTensorData<float>(cell_state),
          output_scratch_buffer, output_ptr, input_zp_ptr, aux_input_zp_ptr,
          output_state_zp_ptr, row_sums_ptr, row_sums_size, compute_row_sums,
          params->asymmetric_quantize_inputs);
    }
  } else {
    for (int b = 0; b < n_batch; b++) {
      const int input_step = n_input;
      const int output_step = output_batch_leading_dim;
      for (int t = 0; t < max_time; t++) {
        // If this is the forward_sequence, step forward, otherwise step
        // backwards.
        const int t_rel = forward_sequence ? t : max_time - t - 1;
        const int time_offset = b * max_time + t_rel;
        const float* input_ptr = tflite::micro::GetTensorData<float>(input) +
                                 time_offset * input_step;
        const float* aux_input_ptr = nullptr;
        if (aux_input) {
          aux_input_ptr = tflite::micro::GetTensorData<float>(aux_input) +
                          time_offset * input_step;
        }
        float* output_ptr = tflite::micro::GetTensorData<float>(output) +
                            time_offset * output_step + output_offset;

        // Offset the {output,cell}_state pointers to the right batch.
        float* output_state_ptr =
            tflite::micro::GetTensorData<float>(output_state) +
            b * output_batch_leading_dim;
        float* cell_state_ptr =
            tflite::micro::GetTensorData<float>(cell_state) + b * n_cell;
        // Offset the scratch pointers to the right batch.
        float* input_gate_scratch_ptr =
            input_gate_scratch ? input_gate_scratch + b * n_cell : nullptr;
        float* forget_gate_scratch_ptr = forget_gate_scratch + b * n_cell;
        float* cell_gate_scratch_ptr = cell_gate_scratch + b * n_cell;
        float* output_gate_scratch_ptr = output_gate_scratch + b * n_cell;

        LstmStepHybrid(
            input_ptr,
            input_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_input_weights),
            input_to_input_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      input_to_input_weights_ledger),
            hybrid_lstm_scales->input_to_input_weights_scale,
            input_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_forget_weights),
            input_to_forget_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      input_to_forget_weights_ledger),
            hybrid_lstm_scales->input_to_forget_weights_scale,
            input_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_cell_weights),
            input_to_cell_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      input_to_cell_weights_ledger),
            hybrid_lstm_scales->input_to_cell_weights_scale,
            input_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_output_weights),
            input_to_output_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      input_to_output_weights_ledger),
            hybrid_lstm_scales->input_to_output_weights_scale, aux_input_ptr,
            aux_input_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      aux_input_to_input_weights),
            hybrid_lstm_scales->aux_input_to_input_weights_scale,
            aux_input_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      aux_input_to_forget_weights),
            hybrid_lstm_scales->aux_input_to_forget_weights_scale,
            aux_input_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      aux_input_to_cell_weights),
            hybrid_lstm_scales->aux_input_to_cell_weights_scale,
            aux_input_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      aux_input_to_output_weights),
            hybrid_lstm_scales->aux_input_to_output_weights_scale,
            recurrent_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_input_weights),
            recurrent_to_input_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      recurrent_to_input_weights_ledger),
            hybrid_lstm_scales->recurrent_to_input_weights_scale,
            recurrent_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_forget_weights),
            recurrent_to_forget_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      recurrent_to_forget_weights_ledger),
            hybrid_lstm_scales->recurrent_to_forget_weights_scale,
            recurrent_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_cell_weights),
            recurrent_to_cell_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      recurrent_to_cell_weights_ledger),
            hybrid_lstm_scales->recurrent_to_cell_weights_scale,
            recurrent_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_output_weights),
            recurrent_to_output_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      recurrent_to_output_weights_ledger),
            hybrid_lstm_scales->recurrent_to_output_weights_scale,
            cell_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(cell_to_input_weights),
            hybrid_lstm_scales->cell_to_input_weights_scale,
            cell_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(cell_to_forget_weights),
            hybrid_lstm_scales->cell_to_forget_weights_scale,
            cell_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(cell_to_output_weights),
            hybrid_lstm_scales->cell_to_output_weights_scale,
            input_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      input_layer_norm_coefficients),
            forget_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      forget_layer_norm_coefficients),
            cell_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      cell_layer_norm_coefficients),
            output_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(
                      output_layer_norm_coefficients),
            input_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(input_gate_bias),
            forget_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(forget_gate_bias),
            cell_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(cell_gate_bias),
            output_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(output_gate_bias),
            projection_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(projection_weights),
            projection_weights_ledger == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<uint8_t>(
                      projection_weights_ledger),
            hybrid_lstm_scales->projection_weights_scale,
            projection_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<float>(projection_bias),
            params,
            /*n_batch=*/1, n_cell, n_input, aux_input_size, n_output,
            output_batch_leading_dim, input_gate_scratch_ptr,
            forget_gate_scratch_ptr, cell_gate_scratch_ptr,
            output_gate_scratch_ptr, scales, input_sf, aux_input_sf,
            output_state_sf, prod_scaling_factors, recovered_cell_weights,
            input_quantized, aux_input_quantized, output_state_quantized,
            cell_state_quantized, output_state_ptr, cell_state_ptr,
            output_scratch_buffer, output_ptr, input_zp_ptr, aux_input_zp_ptr,
            output_state_zp_ptr, row_sums_ptr, row_sums_size, compute_row_sums,
            params->asymmetric_quantize_inputs);
      }
    }
  }

  return kTfLiteOk;
}

TfLiteStatus EvalInteger8x8_16Lstm(
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
    bool forward_sequence, bool time_major,
    const IntegerLstmParameter* integer_lstm_param, int32_t output_state_zp,
    TfLiteEvalTensor* output_state, TfLiteEvalTensor* cell_state,
    TfLiteEvalTensor* output, int16_t* scratch0, int16_t* scratch1,
    int16_t* scratch2, int16_t* scratch3, int8_t* scratch4, int32_t* scratch5) {
  TFLITE_DCHECK(input->dims->size >= 2 && input->dims->size <= 3);
  const int n_input = input->dims->data[input->dims->size - 1];
  int max_time, n_batch;
  if (input->dims->size == 2) {
    max_time = 1;
    n_batch = input->dims->data[0];
  } else {
    max_time = (time_major) ? input->dims->data[0] : input->dims->data[1];
    n_batch = (time_major) ? input->dims->data[1] : input->dims->data[0];
  }

  // n_cell and n_output will be the same size when there is no projection.
  const int n_cell = input_to_output_weights->dims->data[0];
  const int n_output = recurrent_to_output_weights->dims->data[1];

  // Get params for time/batch/sequence.
  const int output_batch_leading_dim =
      output->dims->data[output->dims->size - 1];

  if (time_major) {
    const int input_step = n_batch * n_input;
    const int output_step = n_batch * output_batch_leading_dim;
    for (int t = 0; t < max_time; t++) {
      const int t_rel = t;
      int8_t* output_ptr =
          tflite::micro::GetTensorData<int8_t>(output) + t_rel * output_step;
      const int8_t* input_ptr =
          tflite::micro::GetTensorData<int8_t>(input) + t_rel * input_step;
      LstmStepInteger8x8_16(
          input_ptr,
          input_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_input_weights),
          integer_lstm_param->effective_input_to_input_scale_a,
          integer_lstm_param->effective_input_to_input_scale_b,
          input_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_forget_weights),
          integer_lstm_param->effective_input_to_forget_scale_a,
          integer_lstm_param->effective_input_to_forget_scale_b,
          input_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_cell_weights),
          integer_lstm_param->effective_input_to_cell_scale_a,
          integer_lstm_param->effective_input_to_cell_scale_b,
          input_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(input_to_output_weights),
          integer_lstm_param->effective_input_to_output_scale_a,
          integer_lstm_param->effective_input_to_output_scale_b,
          recurrent_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_input_weights),
          integer_lstm_param->effective_recurrent_to_input_scale_a,
          integer_lstm_param->effective_recurrent_to_input_scale_b,
          recurrent_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_forget_weights),
          integer_lstm_param->effective_recurrent_to_forget_scale_a,
          integer_lstm_param->effective_recurrent_to_forget_scale_b,
          recurrent_to_cell_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(recurrent_to_cell_weights),
          integer_lstm_param->effective_recurrent_to_cell_scale_a,
          integer_lstm_param->effective_recurrent_to_cell_scale_b,
          recurrent_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(
                    recurrent_to_output_weights),
          integer_lstm_param->effective_recurrent_to_output_scale_a,
          integer_lstm_param->effective_recurrent_to_output_scale_b,
          cell_to_input_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(cell_to_input_weights),
          integer_lstm_param->effective_cell_to_input_scale_a,
          integer_lstm_param->effective_cell_to_input_scale_b,
          cell_to_forget_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(cell_to_forget_weights),
          integer_lstm_param->effective_cell_to_forget_scale_a,
          integer_lstm_param->effective_cell_to_forget_scale_b,
          cell_to_output_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(cell_to_output_weights),
          integer_lstm_param->effective_cell_to_output_scale_a,
          integer_lstm_param->effective_cell_to_output_scale_b,
          projection_weights == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int8_t>(projection_weights),
          integer_lstm_param->effective_proj_scale_a,
          integer_lstm_param->effective_proj_scale_b,
          integer_lstm_param->hidden_zp,
          integer_lstm_param->effective_hidden_scale_a,
          integer_lstm_param->effective_hidden_scale_b,
          input_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(
                    input_layer_norm_coefficients),
          integer_lstm_param->layer_norm_input_scale_a,
          integer_lstm_param->layer_norm_input_scale_b,
          forget_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(
                    forget_layer_norm_coefficients),
          integer_lstm_param->layer_norm_forget_scale_a,
          integer_lstm_param->layer_norm_forget_scale_b,
          cell_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(
                    cell_layer_norm_coefficients),
          integer_lstm_param->layer_norm_cell_scale_a,
          integer_lstm_param->layer_norm_cell_scale_b,
          output_layer_norm_coefficients == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int16_t>(
                    output_layer_norm_coefficients),
          integer_lstm_param->layer_norm_output_scale_a,
          integer_lstm_param->layer_norm_output_scale_b,
          input_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int32_t>(input_gate_bias),
          forget_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int32_t>(forget_gate_bias),
          cell_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int32_t>(cell_gate_bias),
          output_gate_bias == nullptr
              ? nullptr
              : tflite::micro::GetTensorData<int32_t>(output_gate_bias),
          integer_lstm_param->quantized_cell_clip,
          integer_lstm_param->quantized_proj_clip,
          integer_lstm_param->cell_scale,
          integer_lstm_param->input_variance_guard,
          integer_lstm_param->forget_variance_guard,
          integer_lstm_param->cell_variance_guard,
          integer_lstm_param->output_variance_guard,
          integer_lstm_param->input_to_forget_effective_bias,
          integer_lstm_param->recurrent_to_forget_effective_bias,
          integer_lstm_param->input_to_cell_effective_bias,
          integer_lstm_param->recurrent_to_cell_effective_bias,
          integer_lstm_param->input_to_output_effective_bias,
          integer_lstm_param->recurrent_to_output_effective_bias,
          integer_lstm_param->input_to_input_effective_bias,
          integer_lstm_param->recurrent_to_input_effective_bias,
          integer_lstm_param->projection_effective_bias, n_batch, n_cell,
          n_input, n_output, tflite::micro::GetTensorData<int8_t>(output_state),
          output_state_zp, tflite::micro::GetTensorData<int16_t>(cell_state),
          output_ptr, scratch0, scratch1, scratch2, scratch3, scratch4,
          scratch5);
    }
  } else {
    for (int b = 0; b < n_batch; b++) {
      const int input_step = n_input;
      const int output_step = output_batch_leading_dim;
      for (int t = 0; t < max_time; t++) {
        // If this is the forward_sequence, step forward, otherwise step
        // backwards.
        const int t_rel = forward_sequence ? t : max_time - t - 1;
        const int time_offset = b * max_time + t_rel;
        const int8_t* input_ptr = tflite::micro::GetTensorData<int8_t>(input) +
                                  time_offset * input_step;
        int8_t* output_ptr = tflite::micro::GetTensorData<int8_t>(output) +
                             time_offset * output_step;

        // Offset the {output,cell}_state pointers to the right batch.
        int8_t* output_state_ptr =
            tflite::micro::GetTensorData<int8_t>(output_state) +
            b * output_batch_leading_dim;
        int16_t* cell_state_ptr =
            tflite::micro::GetTensorData<int16_t>(cell_state) + b * n_cell;

        LstmStepInteger8x8_16(
            input_ptr,
            input_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_input_weights),
            integer_lstm_param->effective_input_to_input_scale_a,
            integer_lstm_param->effective_input_to_input_scale_b,
            input_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_forget_weights),
            integer_lstm_param->effective_input_to_forget_scale_a,
            integer_lstm_param->effective_input_to_forget_scale_b,
            input_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_cell_weights),
            integer_lstm_param->effective_input_to_cell_scale_a,
            integer_lstm_param->effective_input_to_cell_scale_b,
            input_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(input_to_output_weights),
            integer_lstm_param->effective_input_to_output_scale_a,
            integer_lstm_param->effective_input_to_output_scale_b,
            recurrent_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_input_weights),
            integer_lstm_param->effective_recurrent_to_input_scale_a,
            integer_lstm_param->effective_recurrent_to_input_scale_b,
            recurrent_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_forget_weights),
            integer_lstm_param->effective_recurrent_to_forget_scale_a,
            integer_lstm_param->effective_recurrent_to_forget_scale_b,
            recurrent_to_cell_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_cell_weights),
            integer_lstm_param->effective_recurrent_to_cell_scale_a,
            integer_lstm_param->effective_recurrent_to_cell_scale_b,
            recurrent_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(
                      recurrent_to_output_weights),
            integer_lstm_param->effective_recurrent_to_output_scale_a,
            integer_lstm_param->effective_recurrent_to_output_scale_b,
            cell_to_input_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(cell_to_input_weights),
            integer_lstm_param->effective_cell_to_input_scale_a,
            integer_lstm_param->effective_cell_to_input_scale_b,
            cell_to_forget_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(cell_to_forget_weights),
            integer_lstm_param->effective_cell_to_forget_scale_a,
            integer_lstm_param->effective_cell_to_forget_scale_b,
            cell_to_output_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(cell_to_output_weights),
            integer_lstm_param->effective_cell_to_output_scale_a,
            integer_lstm_param->effective_cell_to_output_scale_b,
            projection_weights == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int8_t>(projection_weights),
            integer_lstm_param->effective_proj_scale_a,
            integer_lstm_param->effective_proj_scale_b,
            integer_lstm_param->hidden_zp,
            integer_lstm_param->effective_hidden_scale_a,
            integer_lstm_param->effective_hidden_scale_b,
            input_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(
                      input_layer_norm_coefficients),
            integer_lstm_param->layer_norm_input_scale_a,
            integer_lstm_param->layer_norm_input_scale_b,
            forget_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(
                      forget_layer_norm_coefficients),
            integer_lstm_param->layer_norm_forget_scale_a,
            integer_lstm_param->layer_norm_forget_scale_b,
            cell_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(
                      cell_layer_norm_coefficients),
            integer_lstm_param->layer_norm_cell_scale_a,
            integer_lstm_param->layer_norm_cell_scale_b,
            output_layer_norm_coefficients == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int16_t>(
                      output_layer_norm_coefficients),
            integer_lstm_param->layer_norm_output_scale_a,
            integer_lstm_param->layer_norm_output_scale_b,
            input_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int32_t>(input_gate_bias),
            forget_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int32_t>(forget_gate_bias),
            cell_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int32_t>(cell_gate_bias),
            output_gate_bias == nullptr
                ? nullptr
                : tflite::micro::GetTensorData<int32_t>(output_gate_bias),
            integer_lstm_param->quantized_cell_clip,
            integer_lstm_param->quantized_proj_clip,
            integer_lstm_param->cell_scale,
            integer_lstm_param->input_variance_guard,
            integer_lstm_param->forget_variance_guard,
            integer_lstm_param->cell_variance_guard,
            integer_lstm_param->output_variance_guard,
            integer_lstm_param->input_to_forget_effective_bias,
            integer_lstm_param->recurrent_to_forget_effective_bias,
            integer_lstm_param->input_to_cell_effective_bias,
            integer_lstm_param->recurrent_to_cell_effective_bias,
            integer_lstm_param->input_to_output_effective_bias,
            integer_lstm_param->recurrent_to_output_effective_bias,
            integer_lstm_param->input_to_input_effective_bias,
            integer_lstm_param->recurrent_to_input_effective_bias,
            integer_lstm_param->projection_effective_bias, /*n_batch=*/1,
            n_cell, n_input, n_output, output_state_ptr, output_state_zp,
            cell_state_ptr, output_ptr, scratch0, scratch1, scratch2, scratch3,
            scratch4, scratch5);
      }
    }
  }

  return kTfLiteOk;
}

TfLiteStatus EvalInteger8x8_8Lstm(
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
    TfLiteEvalTensor* output, const IntegerLstmParameter* integer_lstm_param,
    int32_t input_zp, int32_t output_state_zp, int8_t* scratch0,
    int8_t* scratch1, int16_t* scratch2, int16_t* scratch3, int16_t* scratch4,
    int16_t* scratch5, int16_t* scratch6, int16_t* scratch7) {
  TFLITE_DCHECK(input->dims->size >= 2 && input->dims->size <= 3);
  const int n_input = input->dims->data[input->dims->size - 1];
  int max_time, n_batch;
  if (input->dims->size == 2) {
    max_time = 1;
    n_batch = input->dims->data[0];
  } else {
    max_time = input->dims->data[0];
    n_batch = input->dims->data[1];
  }

  // n_cell and n_output will be the same size when there is no projection.
  const int n_cell = input_to_output_weights->dims->data[0];
  const int n_output = recurrent_to_output_weights->dims->data[1];

  // Get params for time/batch/sequence.
  const int output_batch_leading_dim =
      output->dims->data[output->dims->size - 1];
  const int input_step = n_batch * n_input;
  const int output_step = n_batch * output_batch_leading_dim;

  for (int t = 0; t < max_time; t++) {
    const int t_rel = t;
    int8_t* output_ptr =
        tflite::micro::GetTensorData<int8_t>(output) + t_rel * output_step;
    // Input can be int8 asymmetric or int16 symmetric.
    const int8_t* input_ptr =
        tflite::micro::GetTensorData<int8_t>(input) + t_rel * input_step;
    LstmStepInteger8x8_8(
        input_ptr, input_zp,

        input_to_input_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(input_to_input_weights),
        integer_lstm_param->effective_input_to_input_scale_a,
        integer_lstm_param->effective_input_to_input_scale_b,

        input_to_forget_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(input_to_forget_weights),
        integer_lstm_param->effective_input_to_forget_scale_a,
        integer_lstm_param->effective_input_to_forget_scale_b,

        input_to_cell_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(input_to_cell_weights),
        integer_lstm_param->effective_input_to_cell_scale_a,
        integer_lstm_param->effective_input_to_cell_scale_b,

        input_to_output_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(input_to_output_weights),
        integer_lstm_param->effective_input_to_output_scale_a,
        integer_lstm_param->effective_input_to_output_scale_b,

        recurrent_to_input_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(recurrent_to_input_weights),
        integer_lstm_param->effective_recurrent_to_input_scale_a,
        integer_lstm_param->effective_recurrent_to_input_scale_b,

        recurrent_to_forget_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(recurrent_to_forget_weights),
        integer_lstm_param->effective_recurrent_to_forget_scale_a,
        integer_lstm_param->effective_recurrent_to_forget_scale_b,

        recurrent_to_cell_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(recurrent_to_cell_weights),
        integer_lstm_param->effective_recurrent_to_cell_scale_a,
        integer_lstm_param->effective_recurrent_to_cell_scale_b,

        recurrent_to_output_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(recurrent_to_output_weights),
        integer_lstm_param->effective_recurrent_to_output_scale_a,
        integer_lstm_param->effective_recurrent_to_output_scale_b,

        cell_to_input_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(cell_to_input_weights),
        integer_lstm_param->effective_cell_to_input_scale_a,
        integer_lstm_param->effective_cell_to_input_scale_b,

        cell_to_forget_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(cell_to_forget_weights),
        integer_lstm_param->effective_cell_to_forget_scale_a,
        integer_lstm_param->effective_cell_to_forget_scale_b,

        cell_to_output_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(cell_to_output_weights),
        integer_lstm_param->effective_cell_to_output_scale_a,
        integer_lstm_param->effective_cell_to_output_scale_b,

        projection_weights == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int8_t>(projection_weights),
        integer_lstm_param->effective_proj_scale_a,
        integer_lstm_param->effective_proj_scale_b,

        input_layer_norm_coefficients == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int16_t>(
                  input_layer_norm_coefficients),
        integer_lstm_param->layer_norm_input_scale_a,
        integer_lstm_param->layer_norm_input_scale_b,

        forget_layer_norm_coefficients == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int16_t>(
                  forget_layer_norm_coefficients),
        integer_lstm_param->layer_norm_forget_scale_a,
        integer_lstm_param->layer_norm_forget_scale_b,

        cell_layer_norm_coefficients == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int16_t>(
                  cell_layer_norm_coefficients),
        integer_lstm_param->layer_norm_cell_scale_a,
        integer_lstm_param->layer_norm_cell_scale_b,

        output_layer_norm_coefficients == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int16_t>(
                  output_layer_norm_coefficients),
        integer_lstm_param->layer_norm_output_scale_a,
        integer_lstm_param->layer_norm_output_scale_b,

        input_gate_bias == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int32_t>(input_gate_bias),
        forget_gate_bias == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int32_t>(forget_gate_bias),
        cell_gate_bias == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int32_t>(cell_gate_bias),
        output_gate_bias == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int32_t>(output_gate_bias),
        projection_bias == nullptr
            ? nullptr
            : tflite::micro::GetTensorData<int32_t>(projection_bias),

        params, integer_lstm_param->intermediate_scale_a,
        integer_lstm_param->intermediate_scale_b,
        integer_lstm_param->intermediate_zp,
        integer_lstm_param->quantized_cell_clip,
        integer_lstm_param->quantized_proj_clip, n_batch, n_cell, n_input,
        n_output, output_batch_leading_dim,
        tflite::micro::GetTensorData<int8_t>(output_state), output_state_zp,
        tflite::micro::GetTensorData<int16_t>(cell_state), output_ptr, scratch0,
        scratch1, scratch2, scratch3, scratch4, scratch5, scratch6, scratch7);
  }

  return kTfLiteOk;
}

}  // namespace tflite
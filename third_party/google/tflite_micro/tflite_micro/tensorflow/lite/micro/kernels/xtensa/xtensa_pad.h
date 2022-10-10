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
#ifndef TENSORFLOW_LITE_MICRO_KERNELS_XTENSA_XTENSA_PAD_H_
#define TENSORFLOW_LITE_MICRO_KERNELS_XTENSA_XTENSA_PAD_H_

#include <cstdint>

#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/kernels/internal/types.h"
namespace tflite {

struct OpDataPad {
  PadParams params;
  int32_t output_zero_point;
};

struct XtensaPadData {
  OpDataPad reference_op_data;

#if defined(VISION_P6)
  uint8_t* p_context;  // persistent lib context for this instance saved here
  uint32_t context_size;
#endif  // VISION_P6
};

#if defined(VISION_P6)

TfLiteStatus PadPrepareVision(TfLiteContext* context, TfLiteNode* node);

TfLiteStatus PadEvalVision(const XtensaPadData& data,
                           const TfLiteEvalTensor* input,
                           TfLiteEvalTensor* output);
#endif  // VISION_P6

}  // namespace tflite

#endif  // TENSORFLOW_LITE_MICRO_KERNELS_XTENSA_XTENSA_PAD_H_

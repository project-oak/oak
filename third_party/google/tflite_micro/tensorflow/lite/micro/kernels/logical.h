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
#ifndef TENSORFLOW_LITE_MICRO_KERNELS_LOGICAL_H_
#define TENSORFLOW_LITE_MICRO_KERNELS_LOGICAL_H_

#include "tensorflow/lite/c/builtin_op_data.h"
#include "tensorflow/lite/c/common.h"

namespace tflite {
// Input/output tensor index.
extern const int kLogicalInputTensor1;
extern const int kLogicalInputTensor2;
extern const int kLogicalOutputTensor;

TfLiteStatus LogicalImpl(TfLiteContext* context, TfLiteNode* node,
                         bool (*func)(bool, bool));

bool LogicalOr(bool x, bool y);
bool LogicalAnd(bool x, bool y);

}  // namespace tflite

#endif  // TENSORFLOW_LITE_MICRO_KERNELS_LOGICAL_H_

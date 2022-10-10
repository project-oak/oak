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
#ifndef TENSORFLOW_LITE_MICRO_TOOLS_PYTHON_INTERPRETER_NUMPY_UTILS_H_
#define TENSORFLOW_LITE_MICRO_TOOLS_PYTHON_INTERPRETER_NUMPY_UTILS_H_

// Disallow Numpy 1.7 deprecated symbols.
#define NPY_NO_DEPRECATED_API NPY_1_7_API_VERSION
#include <numpy/ndarraytypes.h>

#include "tensorflow/lite/c/c_api_types.h"

namespace tflite {

void* ImportNumpy();
int TfLiteTypeToPyArrayType(TfLiteType tf_lite_type);
TfLiteType TfLiteTypeFromPyType(int py_type);
TfLiteType TfLiteTypeFromPyArray(const PyArrayObject* array);

}  // namespace tflite

#endif

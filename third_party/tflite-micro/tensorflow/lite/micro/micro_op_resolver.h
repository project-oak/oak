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
#ifndef TENSORFLOW_LITE_MICRO_MICRO_OP_RESOLVER_H_
#define TENSORFLOW_LITE_MICRO_MICRO_OP_RESOLVER_H_

#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/tflite_bridge/flatbuffer_conversions_bridge.h"
#include "tensorflow/lite/micro/tflite_bridge/op_resolver_bridge.h"
#include "tensorflow/lite/schema/schema_generated.h"

namespace tflite {

// This is an interface for the OpResolver for TFLiteMicro. The differences from
// the TFLite OpResolver base class are to:
//  * explicitly remove support for Op versions
//  * allow for finer grained registration of the Builtin Ops to reduce code
//    size for TFLiteMicro.
//
// We need an interface class instead of directly using MicroMutableOpResolver
// because MicroMutableOpResolver is a class template with the number of
// registered Ops as the template parameter.
class MicroOpResolver : public TfLiteBridgeOpResolver {
 public:
  // Returns the Op registration struct corresponding to the enum code from the
  // flatbuffer schema. Returns nullptr if the op is not found or if op ==
  // BuiltinOperator_CUSTOM.
  virtual const TfLiteRegistration* FindOp(BuiltinOperator op) const = 0;

  // Returns the Op registration struct corresponding to the custom operator by
  // name.
  virtual const TfLiteRegistration* FindOp(const char* op) const = 0;

  // This implementation exists for compatibility with the OpResolver base class
  // and disregards the version parameter.
  const TfLiteRegistration* FindOp(BuiltinOperator op,
                                   int version) const final {
    return FindOp(op);
  }

  // This implementation exists for compatibility with the OpResolver base class
  // and disregards the version parameter.
  const TfLiteRegistration* FindOp(const char* op, int version) const final {
    return FindOp(op);
  }

  // Returns the operator specific parsing function for the OpData for a
  // BuiltinOperator (if registered), else nullptr.
  virtual TfLiteBridgeBuiltinParseFunction GetOpDataParser(
      BuiltinOperator op) const = 0;

  ~MicroOpResolver() override {}
};

}  // namespace tflite

#endif  // TENSORFLOW_LITE_MICRO_MICRO_OP_RESOLVER_H_

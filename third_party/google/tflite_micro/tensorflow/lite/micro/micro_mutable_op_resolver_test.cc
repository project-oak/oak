/* Copyright 2018 The TensorFlow Authors. All Rights Reserved.

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

#include "tensorflow/lite/micro/micro_mutable_op_resolver.h"

#include "tensorflow/lite/micro/micro_op_resolver.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

namespace tflite {
namespace {
void* MockInit(TfLiteContext* context, const char* buffer, size_t length) {
  // Do nothing.
  return nullptr;
}

void MockFree(TfLiteContext* context, void* buffer) {
  // Do nothing.
}

TfLiteStatus MockPrepare(TfLiteContext* context, TfLiteNode* node) {
  return kTfLiteOk;
}

TfLiteStatus MockInvoke(TfLiteContext* context, TfLiteNode* node) {
  return kTfLiteOk;
}

class MockErrorReporter : public ErrorReporter {
 public:
  MockErrorReporter() : has_been_called_(false) {}
  int Report(const char* format, va_list args) override {
    has_been_called_ = true;
    return 0;
  };

  bool HasBeenCalled() { return has_been_called_; }

  void ResetState() { has_been_called_ = false; }

 private:
  bool has_been_called_;
  TF_LITE_REMOVE_VIRTUAL_DELETE
};

}  // namespace
}  // namespace tflite

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestOperations) {
  using tflite::BuiltinOperator_CONV_2D;
  using tflite::BuiltinOperator_RELU;
  using tflite::MicroMutableOpResolver;
  using tflite::OpResolver;

  static TfLiteRegistration r = {};
  r.init = tflite::MockInit;
  r.free = tflite::MockFree;
  r.prepare = tflite::MockPrepare;
  r.invoke = tflite::MockInvoke;

  MicroMutableOpResolver<1> micro_op_resolver;
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk,
                          micro_op_resolver.AddCustom("mock_custom", &r));

  // Only one AddCustom per operator should return kTfLiteOk.
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteError,
                          micro_op_resolver.AddCustom("mock_custom", &r));

  tflite::MicroOpResolver* resolver = &micro_op_resolver;

  TF_LITE_MICRO_EXPECT_EQ(static_cast<size_t>(1),
                          micro_op_resolver.GetRegistrationLength());

  const TfLiteRegistration* registration =
      resolver->FindOp(BuiltinOperator_RELU);
  TF_LITE_MICRO_EXPECT(nullptr == registration);

  registration = resolver->FindOp("mock_custom");
  TF_LITE_MICRO_EXPECT(nullptr != registration);
  TF_LITE_MICRO_EXPECT(nullptr == registration->init(nullptr, nullptr, 0));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, registration->prepare(nullptr, nullptr));
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, registration->invoke(nullptr, nullptr));

  registration = resolver->FindOp("nonexistent_custom");
  TF_LITE_MICRO_EXPECT(nullptr == registration);
}
TF_LITE_MICRO_TESTS_END

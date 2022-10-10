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

#ifndef TENSORFLOW_LITE_MICRO_BENCHMARKS_MICRO_BENCHMARK_H_
#define TENSORFLOW_LITE_MICRO_BENCHMARKS_MICRO_BENCHMARK_H_

#include <climits>

#include "tensorflow/lite/micro/micro_log.h"
#include "tensorflow/lite/micro/micro_op_resolver.h"
#include "tensorflow/lite/micro/micro_profiler_interface.h"
#include "tensorflow/lite/micro/micro_resource_variable.h"
#include "tensorflow/lite/micro/micro_time.h"
#include "tensorflow/lite/micro/recording_micro_interpreter.h"

namespace tflite {

template <typename inputT>
class MicroBenchmarkRunner {
 public:
  // The lifetimes of model, op_resolver, tensor_arena, profiler must exceed
  // that of the created MicroBenchmarkRunner object.
  MicroBenchmarkRunner(const uint8_t* model,
                       const tflite::MicroOpResolver* op_resolver,
                       uint8_t* tensor_arena, int tensor_arena_size,
                       MicroProfilerInterface* profiler,
                       int num_resource_variables = 0)
      : allocator_(
            RecordingMicroAllocator::Create(tensor_arena, tensor_arena_size)),
        interpreter_(
            GetModel(model), *op_resolver, allocator_,
            MicroResourceVariables::Create(allocator_, num_resource_variables),
            profiler) {
    interpreter_.AllocateTensors();
  }

  void RunSingleIteration() {
    // Run the model on this input and make sure it succeeds.
    TfLiteStatus invoke_status = interpreter_.Invoke();
    if (invoke_status == kTfLiteError) {
      MicroPrintf("Invoke failed.");
    }
  }

  int NumInputs() { return interpreter_.inputs().size(); }

  void SetRandomInput(const int random_seed, int input_index = 0) {
    // The pseudo-random number generator is initialized to a constant seed
    std::srand(random_seed);
    TfLiteTensor* input = interpreter_.input(input_index);

    // Pre-populate input tensor with random values.
    int input_length = input->bytes / sizeof(inputT);
    inputT* input_values = tflite::GetTensorData<inputT>(input);
    for (int i = 0; i < input_length; i++) {
      // Pre-populate input tensor with a random value based on a constant seed.
      input_values[i] = static_cast<inputT>(
          std::rand() % (std::numeric_limits<inputT>::max() -
                         std::numeric_limits<inputT>::min() + 1));
    }
  }

  void SetInput(const inputT* custom_input, int input_index = 0) {
    TfLiteTensor* input = interpreter_.input(input_index);
    inputT* input_buffer = tflite::GetTensorData<inputT>(input);
    int input_length = input->bytes / sizeof(inputT);
    for (int i = 0; i < input_length; i++) {
      input_buffer[i] = custom_input[i];
    }
  }

  void PrintAllocations() const {
    interpreter_.GetMicroAllocator().PrintAllocations();
  }

 private:
  tflite::RecordingMicroAllocator* allocator_;
  tflite::RecordingMicroInterpreter interpreter_;
};

}  // namespace tflite

#endif  // TENSORFLOW_LITE_MICRO_BENCHMARKS_MICRO_BENCHMARK_H_

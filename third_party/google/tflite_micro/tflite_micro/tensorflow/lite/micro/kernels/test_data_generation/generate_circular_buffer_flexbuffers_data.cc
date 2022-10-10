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
#include "flatbuffers/flexbuffers.h"

const char* license =
    "/* Copyright 2021 The TensorFlow Authors. All Rights Reserved.\n"
    "Licensed under the Apache License, Version 2.0 (the \"License\");\n"
    "you may not use this file except in compliance with the License.\n"
    "You may obtain a copy of the License at\n\n"
    "    http://www.apache.org/licenses/LICENSE-2.0\n\n"
    "Unless required by applicable law or agreed to in writing, software\n"
    "distributed under the License is distributed on an \"AS IS\" BASIS,\n"
    "WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n"
    "See the License for the specific language governing permissions and\n"
    "limitations under the License.\n"
    "======================================================================="
    "=======*/\n";

void generate(const char* name) {
  flexbuffers::Builder fbb;
  fbb.Map([&]() { fbb.Int("cycles_max", 1); });
  fbb.Finish();

  // fbb.GetBuffer returns std::Vector<uint8_t> but TfLite passes char arrays
  // for the raw data, and so we reinterpret_cast.
  const uint8_t* init_data =
      reinterpret_cast<const uint8_t*>(fbb.GetBuffer().data());
  int fbb_size = fbb.GetBuffer().size();

  printf("const int g_gen_data_size_%s = %d;\n", name, fbb_size);
  printf("const unsigned char g_gen_data_%s[] = { ", name);
  for (size_t i = 0; i < fbb_size; i++) {
    printf("0x%02x, ", init_data[i]);
  }
  printf("};\n");
}

int main() {
  printf("%s\n", license);
  printf("// This file is generated. See:\n");
  printf("// third_party/tensorflow/lite/micro/kernels/test_data_generation/");
  printf("README.md\n");
  printf("\n");
  printf(
      "#include \"third_party/tensorflow/lite/micro/kernels/"
      "circular_buffer_flexbuffers_generated_data.h\"");
  printf("\n\n");
  generate("circular_buffer_config");
}

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

#include <limits>

#include "tensorflow/lite/c/common.h"
#include "tensorflow/lite/micro/examples/micro_speech/audio_provider.h"
#include "tensorflow/lite/micro/examples/micro_speech/micro_features/micro_model_settings.h"
#include "tensorflow/lite/micro/examples/micro_speech/testdata/no_1000ms_audio_data.h"
#include "tensorflow/lite/micro/examples/micro_speech/testdata/yes_1000ms_audio_data.h"
#include "tensorflow/lite/micro/testing/micro_test.h"

TF_LITE_MICRO_TESTS_BEGIN

TF_LITE_MICRO_TEST(TestAudioProviderMock) {
  int audio_samples_size = 0;
  int16_t* audio_samples = nullptr;
  TfLiteStatus get_status = GetAudioSamples(
      0, kFeatureSliceDurationMs, &audio_samples_size, &audio_samples);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, get_status);
  TF_LITE_MICRO_EXPECT_LE(audio_samples_size, kMaxAudioSampleSize);
  TF_LITE_MICRO_EXPECT(audio_samples != nullptr);
  for (int i = 0; i < audio_samples_size; ++i) {
    TF_LITE_MICRO_EXPECT_EQ(g_yes_1000ms_audio_data[i], audio_samples[i]);
  }

  get_status = GetAudioSamples(500, kFeatureSliceDurationMs,
                               &audio_samples_size, &audio_samples);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, get_status);
  TF_LITE_MICRO_EXPECT_LE(audio_samples_size, kMaxAudioSampleSize);
  TF_LITE_MICRO_EXPECT(audio_samples != nullptr);
  for (int i = 0; i < audio_samples_size; ++i) {
    TF_LITE_MICRO_EXPECT_EQ(g_yes_1000ms_audio_data[i + 8000],
                            audio_samples[i]);
  }

  get_status = GetAudioSamples(1500, kFeatureSliceDurationMs,
                               &audio_samples_size, &audio_samples);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, get_status);
  TF_LITE_MICRO_EXPECT_LE(audio_samples_size, kMaxAudioSampleSize);
  TF_LITE_MICRO_EXPECT(audio_samples != nullptr);
  for (int i = 0; i < audio_samples_size; ++i) {
    TF_LITE_MICRO_EXPECT_EQ(0, audio_samples[i]);
  }

  get_status = GetAudioSamples(12250, kFeatureSliceDurationMs,
                               &audio_samples_size, &audio_samples);
  TF_LITE_MICRO_EXPECT_EQ(kTfLiteOk, get_status);
  TF_LITE_MICRO_EXPECT_LE(audio_samples_size, kMaxAudioSampleSize);
  TF_LITE_MICRO_EXPECT(audio_samples != nullptr);
  for (int i = 0; i < audio_samples_size; ++i) {
    TF_LITE_MICRO_EXPECT_EQ(g_no_1000ms_audio_data[i + 4000], audio_samples[i]);
  }
}

TF_LITE_MICRO_TESTS_END

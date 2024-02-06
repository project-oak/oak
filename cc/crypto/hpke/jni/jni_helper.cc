/*
 * Copyright 2023 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "cc/crypto/hpke/jni/jni_helper.h"

#include <memory>
#include <string>
#include <vector>

std::string convert_jbytearray_to_string(JNIEnv* env, jbyteArray arr) {
  int len = env->GetArrayLength(arr);
  char* buf = new char[len];
  std::unique_ptr<char[]> buf_uptr(buf);
  env->GetByteArrayRegion(arr, 0, len, reinterpret_cast<jbyte*>(buf));
  std::string result(buf, len);
  return result;
}

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

#include "../recipient_context.h"
#include "absl/status/statusor.h"
#include "com_google_oak_crypto_hpke_KeyPair.h"

JNIEXPORT jobject JNICALL
Java_com_google_oak_crypto_hpke_KeyPair_nativeGenerate(JNIEnv* env,
                                                       jclass obj) {
  absl::StatusOr<::oak::crypto::KeyPair> kp_status =
      oak::crypto::KeyPair::Generate();
  if (!kp_status.ok()) {
    return {};
  }
  std::string private_key = kp_status->private_key;
  jbyteArray private_key_arr = env->NewByteArray(private_key.length());
  env->SetByteArrayRegion(private_key_arr, 0, private_key.length(),
                          reinterpret_cast<const jbyte*>(private_key.c_str()));

  std::string public_key = kp_status->public_key;
  jbyteArray public_key_arr = env->NewByteArray(public_key.length());
  env->SetByteArrayRegion(public_key_arr, 0, public_key.length(),
                          reinterpret_cast<const jbyte*>(public_key.c_str()));

  jclass key_pair_class = env->FindClass("com/google/oak/crypto/hpke/KeyPair");
  jmethodID key_pair_constructor =
      env->GetMethodID(key_pair_class, "<init>", "([B[B)V");
  jobject key_pair = env->NewObject(key_pair_class, key_pair_constructor,
                                    private_key_arr, public_key_arr);
  return key_pair;
}
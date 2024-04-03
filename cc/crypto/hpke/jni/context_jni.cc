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
#include "../sender_context.h"
#include "absl/status/statusor.h"
#include "com_google_oak_crypto_hpke_RecipientContext.h"
#include "com_google_oak_crypto_hpke_SenderContext.h"
#include "jni_helper.h"

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_SenderContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray nonce, jbyteArray plaintext,
    jbyteArray associated_data) {
  if (nonce == NULL || plaintext == NULL || associated_data == NULL) {
    return {};
  }

  std::string nonce_str = convert_jbytearray_to_string(env, nonce);
  std::string plaintext_str = convert_jbytearray_to_string(env, plaintext);
  std::string associated_data_str =
      convert_jbytearray_to_string(env, associated_data);

  jclass sender_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_context_class, "nativePtr", "J");
  oak::crypto::SenderContext* sender_context =
      (oak::crypto::SenderContext*)(env->GetLongField(obj, fid));
  if (sender_context == NULL) {
    return {};
  }

  const std::vector<uint8_t> nonce_bytes(nonce_str.begin(), nonce_str.end());
  absl::StatusOr<std::string> result =
      sender_context->Seal(nonce_bytes, plaintext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_SenderContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray nonce, jbyteArray ciphertext,
    jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  std::string nonce_str = convert_jbytearray_to_string(env, nonce);
  std::string ciphertext_str = convert_jbytearray_to_string(env, ciphertext);
  std::string associated_data_str =
      convert_jbytearray_to_string(env, associated_data);

  jclass sender_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_context_class, "nativePtr", "J");
  oak::crypto::SenderContext* sender_context =
      (oak::crypto::SenderContext*)(env->GetLongField(obj, fid));
  if (sender_context == NULL) {
    return {};
  }

  const std::vector<uint8_t> nonce_bytes(nonce_str.begin(), nonce_str.end());
  absl::StatusOr<std::string> result =
      sender_context->Open(nonce_bytes, ciphertext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_RecipientContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray nonce, jbyteArray ciphertext,
    jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  std::string nonce_str = convert_jbytearray_to_string(env, nonce);
  std::string ciphertext_str = convert_jbytearray_to_string(env, ciphertext);
  std::string associated_data_str =
      convert_jbytearray_to_string(env, associated_data);

  jclass recipient_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_context_class, "nativePtr", "J");
  oak::crypto::RecipientContext* recipient_context =
      (oak::crypto::RecipientContext*)(env->GetLongField(obj, fid));
  if (recipient_context == NULL) {
    return {};
  }

  const std::vector<uint8_t> nonce_bytes(nonce_str.begin(), nonce_str.end());
  absl::StatusOr<std::string> result =
      recipient_context->Open(nonce_bytes, ciphertext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_RecipientContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray nonce, jbyteArray plaintext,
    jbyteArray associated_data) {
  if (nonce == NULL || plaintext == NULL || associated_data == NULL) {
    return {};
  }

  std::string nonce_str = convert_jbytearray_to_string(env, nonce);
  std::string plaintext_str = convert_jbytearray_to_string(env, plaintext);
  std::string associated_data_str =
      convert_jbytearray_to_string(env, associated_data);

  jclass recipient_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_context_class, "nativePtr", "J");
  oak::crypto::RecipientContext* recipient_context =
      (oak::crypto::RecipientContext*)(env->GetLongField(obj, fid));
  if (recipient_context == NULL) {
    return {};
  }

  const std::vector<uint8_t> nonce_bytes(nonce_str.begin(), nonce_str.end());
  absl::StatusOr<std::string> result =
      recipient_context->Seal(nonce_bytes, plaintext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_SenderContext_nativeDestroy(JNIEnv* env,
                                                            jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::SenderContext* sender_context =
      (oak::crypto::SenderContext*)(env->GetLongField(obj, fid));
  if (sender_context == NULL) {
    return;
  }
  delete sender_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_RecipientContext_nativeDestroy(JNIEnv* env,
                                                               jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::RecipientContext* recipient_context =
      (oak::crypto::RecipientContext*)(env->GetLongField(obj, fid));
  if (recipient_context == NULL) {
    return;
  }
  delete recipient_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}

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
#include "com_google_oak_crypto_hpke_Context_RecipientRequestContext.h"
#include "com_google_oak_crypto_hpke_Context_RecipientResponseContext.h"
#include "com_google_oak_crypto_hpke_Context_SenderRequestContext.h"
#include "com_google_oak_crypto_hpke_Context_SenderResponseContext.h"
#include "jni_helper.h"

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderRequestContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray plaintext, jbyteArray associated_data) {
  if (plaintext == NULL || associated_data == NULL) {
    return {};
  }

  std::string plaintext_str = convert_jbytearray_to_string(env, plaintext);
  std::string associated_data_str = convert_jbytearray_to_string(env, associated_data);

  jclass sender_request_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_request_context_class, "nativePtr", "J");
  oak::crypto::SenderRequestContext* sender_request_context =
      (oak::crypto::SenderRequestContext*)(env->GetLongField(obj, fid));
  if (sender_request_context == NULL) {
    return {};
  }

  absl::StatusOr<std::string> result =
      sender_request_context->Seal(plaintext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderResponseContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray ciphertext, jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  std::string ciphertext_str = convert_jbytearray_to_string(env, ciphertext);
  std::string associated_data_str = convert_jbytearray_to_string(env, associated_data);

  jclass sender_response_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_response_context_class, "nativePtr", "J");
  oak::crypto::SenderResponseContext* sender_response_context =
      (oak::crypto::SenderResponseContext*)(env->GetLongField(obj, fid));
  if (sender_response_context == NULL) {
    return {};
  }

  absl::StatusOr<std::string> result =
      sender_response_context->Open(ciphertext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientRequestContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray ciphertext, jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  std::string ciphertext_str = convert_jbytearray_to_string(env, ciphertext);
  std::string associated_data_str = convert_jbytearray_to_string(env, associated_data);

  jclass recipient_request_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_request_context_class, "nativePtr", "J");
  oak::crypto::RecipientRequestContext* recipient_request_context =
      (oak::crypto::RecipientRequestContext*)(env->GetLongField(obj, fid));
  if (recipient_request_context == NULL) {
    return {};
  }

  absl::StatusOr<std::string> result =
      recipient_request_context->Open(ciphertext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientResponseContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray plaintext, jbyteArray associated_data) {
  if (plaintext == NULL || associated_data == NULL) {
    return {};
  }

  std::string plaintext_str = convert_jbytearray_to_string(env, plaintext);
  std::string associated_data_str = convert_jbytearray_to_string(env, associated_data);

  jclass recipient_response_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_response_context_class, "nativePtr", "J");
  oak::crypto::RecipientResponseContext* recipient_response_context =
      (oak::crypto::RecipientResponseContext*)(env->GetLongField(obj, fid));
  if (recipient_response_context == NULL) {
    return {};
  }

  absl::StatusOr<std::string> result =
      recipient_response_context->Seal(plaintext_str, associated_data_str);
  if (!result.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(result->length());
  env->SetByteArrayRegion(ret, 0, result->length(),
                          reinterpret_cast<const jbyte*>(result->c_str()));
  return ret;
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderRequestContext_nativeDestroy(JNIEnv* env,
                                                                                jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::SenderRequestContext* sender_request_context =
      (oak::crypto::SenderRequestContext*)(env->GetLongField(obj, fid));
  if (sender_request_context == NULL) {
    return;
  }
  delete sender_request_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderResponseContext_nativeDestroy(JNIEnv* env,
                                                                                 jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::SenderResponseContext* sender_response_context =
      (oak::crypto::SenderResponseContext*)(env->GetLongField(obj, fid));
  if (sender_response_context == NULL) {
    return;
  }
  delete sender_response_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientRequestContext_nativeDestroy(JNIEnv* env,
                                                                                   jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::RecipientRequestContext* recipient_request_context =
      (oak::crypto::RecipientRequestContext*)(env->GetLongField(obj, fid));
  if (recipient_request_context == NULL) {
    return;
  }
  delete recipient_request_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}

JNIEXPORT void JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientResponseContext_nativeDestroy(JNIEnv* env,
                                                                                    jobject obj) {
  jclass context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(context_class, "nativePtr", "J");
  oak::crypto::RecipientResponseContext* recipient_response_context =
      (oak::crypto::RecipientResponseContext*)(env->GetLongField(obj, fid));
  if (recipient_response_context == NULL) {
    return;
  }
  delete recipient_response_context;
  // Set nativePtr's value to 0 in the java object after deleting in native.
  env->SetLongField(obj, fid, 0);
}
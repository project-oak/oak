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

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderRequestContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray plaintext, jbyteArray associated_data) {
  if (plaintext == NULL || associated_data == NULL) {
    return {};
  }

  int plaintext_len = env->GetArrayLength(plaintext);
  char* plaintext_buf = new char[plaintext_len];
  env->GetByteArrayRegion(plaintext, 0, plaintext_len, reinterpret_cast<jbyte*>(plaintext_buf));

  int associated_data_len = env->GetArrayLength(associated_data);
  char* associated_data_buf = new char[associated_data_len];
  env->GetByteArrayRegion(associated_data, 0, associated_data_len,
                          reinterpret_cast<jbyte*>(associated_data_buf));

  // TODO(#3642): Call the c++ hpke implementation to perform the seal and get the return value.
  jclass sender_request_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_request_context_class, "nativePtr", "J");
  oak::crypto::SenderRequestContext* sender_request_context =
      (oak::crypto::SenderRequestContext*)(env->GetLongField(obj, fid));
  if (sender_request_context == NULL) {
    return {};
  }

  int len = plaintext_len;
  jbyteArray ret = env->NewByteArray(len);
  env->SetByteArrayRegion(ret, 0, len, reinterpret_cast<const jbyte*>(plaintext_buf));
  delete[] plaintext_buf;
  delete[] associated_data_buf;
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024SenderResponseContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray ciphertext, jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  int ciphertext_len = env->GetArrayLength(ciphertext);
  char* ciphertext_buf = new char[ciphertext_len];
  env->GetByteArrayRegion(ciphertext, 0, ciphertext_len, reinterpret_cast<jbyte*>(ciphertext_buf));

  int associated_data_len = env->GetArrayLength(associated_data);
  char* associated_data_buf = new char[associated_data_len];
  env->GetByteArrayRegion(associated_data, 0, associated_data_len,
                          reinterpret_cast<jbyte*>(associated_data_buf));

  // TODO(#3642): Call the c++ hpke implementation to perform the open and get the return value.
  jclass sender_response_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(sender_response_context_class, "nativePtr", "J");
  oak::crypto::SenderResponseContext* sender_response_context =
      (oak::crypto::SenderResponseContext*)(env->GetLongField(obj, fid));
  if (sender_response_context == NULL) {
    return {};
  }

  int len = ciphertext_len;
  jbyteArray ret = env->NewByteArray(len);
  env->SetByteArrayRegion(ret, 0, len, reinterpret_cast<const jbyte*>(ciphertext_buf));
  delete[] ciphertext_buf;
  delete[] associated_data_buf;
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientRequestContext_nativeOpen(
    JNIEnv* env, jobject obj, jbyteArray ciphertext, jbyteArray associated_data) {
  if (ciphertext == NULL || associated_data == NULL) {
    return {};
  }

  int ciphertext_len = env->GetArrayLength(ciphertext);
  char* ciphertext_buf = new char[ciphertext_len];
  env->GetByteArrayRegion(ciphertext, 0, ciphertext_len, reinterpret_cast<jbyte*>(ciphertext_buf));

  int associated_data_len = env->GetArrayLength(associated_data);
  char* associated_data_buf = new char[associated_data_len];
  env->GetByteArrayRegion(associated_data, 0, associated_data_len,
                          reinterpret_cast<jbyte*>(associated_data_buf));

  // TODO(#3642): Call the c++ hpke implementation to perform the open and get the return value.
  jclass recipient_request_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_request_context_class, "nativePtr", "J");
  oak::crypto::RecipientRequestContext* recipient_request_context =
      (oak::crypto::RecipientRequestContext*)(env->GetLongField(obj, fid));
  if (recipient_request_context == NULL) {
    return {};
  }

  int len = ciphertext_len;
  jbyteArray ret = env->NewByteArray(len);
  env->SetByteArrayRegion(ret, 0, len, reinterpret_cast<const jbyte*>(ciphertext_buf));
  delete[] ciphertext_buf;
  delete[] associated_data_buf;
  return ret;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Context_00024RecipientResponseContext_nativeSeal(
    JNIEnv* env, jobject obj, jbyteArray plaintext, jbyteArray associated_data) {
  if (plaintext == NULL || associated_data == NULL) {
    return {};
  }

  int plaintext_len = env->GetArrayLength(plaintext);
  char* plaintext_buf = new char[plaintext_len];
  env->GetByteArrayRegion(plaintext, 0, plaintext_len, reinterpret_cast<jbyte*>(plaintext_buf));

  int associated_data_len = env->GetArrayLength(associated_data);
  char* associated_data_buf = new char[associated_data_len];
  env->GetByteArrayRegion(associated_data, 0, associated_data_len,
                          reinterpret_cast<jbyte*>(associated_data_buf));

  // TODO(#3642): Call the c++ hpke implementation to perform the seal and get the return value.
  jclass recipient_response_context_class = env->GetObjectClass(obj);
  jfieldID fid = env->GetFieldID(recipient_response_context_class, "nativePtr", "J");
  oak::crypto::RecipientResponseContext* recipient_response_context =
      (oak::crypto::RecipientResponseContext*)(env->GetLongField(obj, fid));
  if (recipient_response_context == NULL) {
    return {};
  }

  int len = plaintext_len;
  jbyteArray ret = env->NewByteArray(len);
  env->SetByteArrayRegion(ret, 0, len, reinterpret_cast<const jbyte*>(plaintext_buf));
  delete[] plaintext_buf;
  delete[] associated_data_buf;
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
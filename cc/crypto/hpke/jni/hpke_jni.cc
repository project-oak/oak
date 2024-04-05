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

#include <memory>

#include "../recipient_context.h"
#include "../sender_context.h"
#include "../utils.h"
#include "absl/status/statusor.h"
#include "com_google_oak_crypto_hpke_Hpke.h"
#include "jni_helper.h"

JNIEXPORT jobject JNICALL
Java_com_google_oak_crypto_hpke_Hpke_nativeSetupBaseSender(
    JNIEnv* env, jclass obj, jbyteArray serialized_recipient_public_key,
    jbyteArray info) {
  if (serialized_recipient_public_key == NULL || info == NULL) {
    return {};
  }

  std::string serialized_recipient_public_key_str =
      convert_jbytearray_to_string(env, serialized_recipient_public_key);
  std::string info_str = convert_jbytearray_to_string(env, info);

  absl::StatusOr<std::unique_ptr<::oak::crypto::SenderContext>>
      native_sender_context = oak::crypto::SetupBaseSender(
          serialized_recipient_public_key_str, info_str);
  if (!native_sender_context.ok()) {
    return {};
  }

  int serialized_encapsulated_public_key_len =
      (*native_sender_context)->GetSerializedEncapsulatedPublicKey().size();
  jbyteArray serialized_encapsulated_public_key =
      env->NewByteArray(serialized_encapsulated_public_key_len);
  env->SetByteArrayRegion(
      serialized_encapsulated_public_key, 0,
      serialized_encapsulated_public_key_len,
      reinterpret_cast<const jbyte*>((*native_sender_context)
                                         ->GetSerializedEncapsulatedPublicKey()
                                         .data()));

  jclass sender_context_class =
      env->FindClass("com/google/oak/crypto/hpke/SenderContext");
  jmethodID sender_context_constructor =
      env->GetMethodID(sender_context_class, "<init>", "([BJ)V");
  jobject sender_context =
      env->NewObject(sender_context_class, sender_context_constructor,
                     serialized_encapsulated_public_key,
                     (long)native_sender_context->release());

  return sender_context;
}

JNIEXPORT jobject JNICALL
Java_com_google_oak_crypto_hpke_Hpke_nativeSetupBaseRecipient(
    JNIEnv* env, jclass obj, jbyteArray serialized_encapsulated_public_key,
    jobject recipient_key_pair, jbyteArray info) {
  if (serialized_encapsulated_public_key == NULL || info == NULL ||
      recipient_key_pair == NULL) {
    return {};
  }

  std::string serialized_encapsulated_public_key_str =
      convert_jbytearray_to_string(env, serialized_encapsulated_public_key);
  std::string info_str = convert_jbytearray_to_string(env, info);

  jclass key_pair_class = env->GetObjectClass(recipient_key_pair);
  jfieldID private_key_fid =
      env->GetFieldID(key_pair_class, "privateKey", "[B");
  jbyteArray private_key = static_cast<jbyteArray>(
      env->GetObjectField(recipient_key_pair, private_key_fid));
  std::string private_key_str = convert_jbytearray_to_string(env, private_key);

  jfieldID public_key_fid = env->GetFieldID(key_pair_class, "publicKey", "[B");
  jbyteArray public_key = static_cast<jbyteArray>(
      env->GetObjectField(recipient_key_pair, public_key_fid));
  std::string public_key_str = convert_jbytearray_to_string(env, public_key);

  oak::crypto::KeyPair key_pair;
  key_pair.public_key = public_key_str;
  key_pair.private_key = private_key_str;

  absl::StatusOr<std::unique_ptr<::oak::crypto::RecipientContext>>
      native_recipient_context = oak::crypto::SetupBaseRecipient(
          serialized_encapsulated_public_key_str, key_pair, info_str);
  if (!native_recipient_context.ok()) {
    return {};
  }

  jclass recipient_context_class =
      env->FindClass("com/google/oak/crypto/hpke/RecipientContext");
  jmethodID recipient_context_constructor =
      env->GetMethodID(recipient_context_class, "<init>", "(J)V");
  jobject recipient_context =
      env->NewObject(recipient_context_class, recipient_context_constructor,
                     (long)native_recipient_context->release());

  return recipient_context;
}

JNIEXPORT jbyteArray JNICALL
Java_com_google_oak_crypto_hpke_Hpke_nativeGenerateRandomNonce(JNIEnv* env,
                                                               jclass obj) {
  absl::StatusOr<std::vector<uint8_t>> nonce =
      oak::crypto::GenerateRandomNonce();
  if (!nonce.ok()) {
    return {};
  }

  jbyteArray ret = env->NewByteArray(nonce->size());
  env->SetByteArrayRegion(ret, 0, nonce->size(),
                          reinterpret_cast<const jbyte*>(&nonce->front()));
  return ret;
}

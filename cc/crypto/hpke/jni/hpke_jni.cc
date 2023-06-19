#include "com_google_oak_crypto_hpke_Hpke.h"
#include "../hpke.h"

JNIEXPORT jobject JNICALL Java_com_google_oak_crypto_hpke_Hpke_nativeSetupBaseSender
  (JNIEnv* env, jclass obj, jbyteArray serialized_recipient_public_key, jbyteArray info) {
  jbyteArray serialized_encapsulated_public_key = env->NewByteArray(1);

  // TODO(#3642): Use the result of setup_base_sender instead of manually making the context.
  oak::crypto::SenderRequestContext* native_sender_request_context = new oak::crypto::SenderRequestContext();
  jclass sender_request_context_class = env->FindClass("com/google/oak/crypto/hpke/Context$SenderRequestContext");
  jmethodID sender_request_context_constructor = env->GetMethodID(sender_request_context_class, "<init>", "(J)V");
  jobject sender_request_context = env->NewObject(sender_request_context_class, sender_request_context_constructor, (long)native_sender_request_context);

  oak::crypto::SenderResponseContext* native_sender_response_context = new oak::crypto::SenderResponseContext();
  jclass sender_response_context_class = env->FindClass("com/google/oak/crypto/hpke/Context$SenderResponseContext");
  jmethodID sender_response_context_constructor = env->GetMethodID(sender_response_context_class, "<init>", "(J)V");
  jobject sender_response_context = env->NewObject(sender_response_context_class, sender_response_context_constructor, (long)native_sender_response_context);

  jclass cls = env->FindClass("com/google/oak/crypto/hpke/Hpke$SenderContext");
  jmethodID constructor = env->GetMethodID(cls, "<init>", "([BLcom/google/oak/crypto/hpke/Context$SenderRequestContext;Lcom/google/oak/crypto/hpke/Context$SenderResponseContext;)V");
  jobject sender_context = env->NewObject(cls, constructor, serialized_encapsulated_public_key, sender_request_context, sender_response_context);
  return sender_context;
}

JNIEXPORT jobject JNICALL Java_com_google_oak_crypto_hpke_Hpke_nativeSetupBaseRecipient
  (JNIEnv* env, jclass obj, jbyteArray serialized_encapsulated_public_key, jobject recipient_key_pair, jbyteArray info) {
  // TODO(#3642): Use the result of setup_base_recipient instead of manually making the context.
  oak::crypto::RecipientRequestContext* native_recipient_request_context = new oak::crypto::RecipientRequestContext();
  jclass recipient_request_context_class = env->FindClass("com/google/oak/crypto/hpke/Context$RecipientRequestContext");
  jmethodID recipient_request_context_constructor = env->GetMethodID(recipient_request_context_class, "<init>", "(J)V");
  jobject recipient_request_context = env->NewObject(recipient_request_context_class, recipient_request_context_constructor, (long)native_recipient_request_context);

  oak::crypto::RecipientResponseContext* native_recipient_response_context = new oak::crypto::RecipientResponseContext();
  jclass recipient_response_context_class = env->FindClass("com/google/oak/crypto/hpke/Context$RecipientResponseContext");
  jmethodID recipient_response_context_constructor = env->GetMethodID(recipient_response_context_class, "<init>", "(J)V");
  jobject recipient_response_context = env->NewObject(recipient_response_context_class, recipient_response_context_constructor, (long)native_recipient_response_context);

  jclass cls = env->FindClass("com/google/oak/crypto/hpke/Hpke$RecipientContext");
  jmethodID constructor = env->GetMethodID(cls, "<init>", "(Lcom/google/oak/crypto/hpke/Context$RecipientRequestContext;Lcom/google/oak/crypto/hpke/Context$RecipientResponseContext;)V");
  jobject recipient_context = env->NewObject(cls, constructor, recipient_request_context, recipient_response_context);
  return recipient_context;
}
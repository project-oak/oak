/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class com_google_oak_crypto_hpke_RecipientContext */

#ifndef _Included_com_google_oak_crypto_hpke_RecipientContext
#define _Included_com_google_oak_crypto_hpke_RecipientContext
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     com_google_oak_crypto_hpke_RecipientContext
 * Method:    nativeOpen
 * Signature: ([B[B)[B
 */
JNIEXPORT jbyteArray JNICALL Java_com_google_oak_crypto_hpke_RecipientContext_nativeOpen
  (JNIEnv *, jobject, jbyteArray, jbyteArray);

/*
 * Class:     com_google_oak_crypto_hpke_RecipientContext
 * Method:    nativeSeal
 * Signature: ([B[B)[B
 */
JNIEXPORT jbyteArray JNICALL Java_com_google_oak_crypto_hpke_RecipientContext_nativeSeal
  (JNIEnv *, jobject, jbyteArray, jbyteArray);

/*
 * Class:     com_google_oak_crypto_hpke_RecipientContext
 * Method:    nativeDestroy
 * Signature: ()V
 */
JNIEXPORT void JNICALL Java_com_google_oak_crypto_hpke_RecipientContext_nativeDestroy
  (JNIEnv *, jobject);

#ifdef __cplusplus
}
#endif
#endif

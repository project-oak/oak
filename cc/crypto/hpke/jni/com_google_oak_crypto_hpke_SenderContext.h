/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class com_google_oak_crypto_hpke_SenderContext */

#ifndef _Included_com_google_oak_crypto_hpke_SenderContext
#define _Included_com_google_oak_crypto_hpke_SenderContext
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     com_google_oak_crypto_hpke_SenderContext
 * Method:    nativeGenerateNonce
 * Signature: ()[B
 */
JNIEXPORT jbyteArray JNICALL Java_com_google_oak_crypto_hpke_SenderContext_nativeGenerateNonce
  (JNIEnv *, jobject);

/*
 * Class:     com_google_oak_crypto_hpke_SenderContext
 * Method:    nativeSeal
 * Signature: ([B[B)[B
 */
JNIEXPORT jbyteArray JNICALL Java_com_google_oak_crypto_hpke_SenderContext_nativeSeal
  (JNIEnv *, jobject, jbyteArray, jbyteArray);

/*
 * Class:     com_google_oak_crypto_hpke_SenderContext
 * Method:    nativeOpen
 * Signature: ([B[B)[B
 */
JNIEXPORT jbyteArray JNICALL Java_com_google_oak_crypto_hpke_SenderContext_nativeOpen
  (JNIEnv *, jobject, jbyteArray, jbyteArray);

/*
 * Class:     com_google_oak_crypto_hpke_SenderContext
 * Method:    nativeDestroy
 * Signature: ()V
 */
JNIEXPORT void JNICALL Java_com_google_oak_crypto_hpke_SenderContext_nativeDestroy
  (JNIEnv *, jobject);

#ifdef __cplusplus
}
#endif
#endif

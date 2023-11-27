//
// Copyright 2023 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.crypto.hpke;

import com.google.oak.util.Result;

public final class SenderContext implements AutoCloseable {
  private final byte[] serializedEncapsulatedPublicKey;

  static {
    System.loadLibrary("hpke-jni");
  }
  private final long nativePtr;
  public SenderContext(byte[] serializedEncapsulatedPublicKey, long nativePtr) {
    this.serializedEncapsulatedPublicKey = serializedEncapsulatedPublicKey;
    this.nativePtr = nativePtr;
  }

  private native byte[] nativeGenerateNonce();
  private native byte[] nativeSeal(final byte[] nonce, final byte[] plaintext, final byte[] associatedData);
  private native byte[] nativeOpen(final byte[] ciphertext, final byte[] associatedData);
  private native void nativeDestroy();

  public final byte[] getSerializedEncapsulatedPublicKey() {
    return serializedEncapsulatedPublicKey;
  }

  /**
   * Generates an AEAD nonce used by AEAD encryption scheme.
   * <https://datatracker.ietf.org/doc/html/rfc5116>
   */
  public final Result<byte[], Exception> generateNonce() {
    byte[] nativeResult = nativeGenerateNonce();
    if (nativeResult == null) {
      return Result.error(new Exception("SenderContext generateNonce failed"));
    }
    return Result.success(nativeResult);
  }

  /**
   * Encrypts message with associated data using AEAD.
   * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
   */
  public final Result<byte[], Exception> seal(final byte[] nonce, final byte[] plaintext, final byte[] associatedData) {
    byte[] nativeResult = nativeSeal(nonce, plaintext, associatedData);
    if (nativeResult == null) {
      return Result.error(new Exception("SenderContext seal failed"));
    }
    return Result.success(nativeResult);
  }

  /**
   * Decrypts response message and validates associated data using AEAD as part of bidirectional
   * communication. <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
   */
  public final Result<byte[], Exception> open(
      final byte[] ciphertext, final byte[] associatedData) {
    byte[] nativeResult = nativeOpen(ciphertext, associatedData);
    if (nativeResult == null) {
      return Result.error(new Exception("SenderContext open failed"));
    }
    return Result.success(nativeResult);
  }

  /**
   * Destroys any allocated native resources for this object.
   */
  @Override
  public void close() {
    nativeDestroy();
  }
}

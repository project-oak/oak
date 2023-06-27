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

// TODO(#3642): Implement Java Hybrid Encryption.
public final class Context {
  public static final class SenderRequestContext implements AutoCloseable {
    static {
      System.loadLibrary("hpke-jni");
    }
    private final long nativePtr;
    public SenderRequestContext(long nativePtr) {
      this.nativePtr = nativePtr;
    }

    private native byte[] nativeSeal(final byte[] plaintext, final byte[] associatedData);

    private native void nativeDestroy();

    /**
     * Encrypts message with associated data using AEAD.
     * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
     */
    public final Result<byte[], Exception> seal(
        final byte[] plaintext, final byte[] associatedData) {
      byte[] nativeResult = nativeSeal(plaintext, associatedData);
      if (nativeResult == null) {
        return Result.error(new Exception("SenderRequestContext seal failed."));
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

  public static final class SenderResponseContext implements AutoCloseable {
    static {
      System.loadLibrary("hpke-jni");
    }
    private final long nativePtr;
    public SenderResponseContext(long nativePtr) {
      this.nativePtr = nativePtr;
    }

    private native byte[] nativeOpen(final byte[] ciphertext, final byte[] associatedData);

    private native void nativeDestroy();

    /**
     * Decrypts response message and validates associated data using AEAD as part of bidirectional
     * communication. <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
     */
    public final Result<byte[], Exception> open(
        final byte[] ciphertext, final byte[] associatedData) {
      byte[] nativeResult = nativeOpen(ciphertext, associatedData);
      if (nativeResult == null) {
        return Result.error(new Exception("SenderResponseContext open failed."));
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
  };

  public static final class RecipientRequestContext implements AutoCloseable {
    static {
      System.loadLibrary("hpke-jni");
    }
    private final long nativePtr;
    public RecipientRequestContext(long nativePtr) {
      this.nativePtr = nativePtr;
    }

    private native byte[] nativeOpen(final byte[] ciphertext, final byte[] associatedData);

    private native void nativeDestroy();

    /**
     * Decrypts message and validates associated data using AEAD.
     * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
     */
    public final Result<byte[], Exception> open(
        final byte[] ciphertext, final byte[] associatedData) {
      byte[] nativeResult = nativeOpen(ciphertext, associatedData);
      if (nativeResult == null) {
        return Result.error(new Exception("RecipientRequestContext open failed."));
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
  };

  public static final class RecipientResponseContext implements AutoCloseable {
    static {
      System.loadLibrary("hpke-jni");
    }
    private final long nativePtr;
    public RecipientResponseContext(long nativePtr) {
      this.nativePtr = nativePtr;
    }

    private native byte[] nativeSeal(final byte[] plaintext, final byte[] associatedData);

    private native void nativeDestroy();

    /**
     * Encrypts response message with associated data using AEAD as part of bidirectional
     * communication. <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
     */
    public final Result<byte[], Exception> seal(
        final byte[] plaintext, final byte[] associatedData) {
      byte[] nativeResult = nativeSeal(plaintext, associatedData);
      if (nativeResult == null) {
        return Result.error(new Exception("RecipientResponseContext seal failed."));
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
  };

  private Context() {}
}

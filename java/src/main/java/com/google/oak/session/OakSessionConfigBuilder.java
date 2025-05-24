//
// Copyright 2025 The Project Oak Authors
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

package com.google.oak.session;
import java.util.concurrent.atomic.AtomicLong;

/**
 * SessionConfigBuilder wrapper.
 *
 * This provides a wrapper around a native SessionConfigBuilder.
 *
 * The full API is not yet exposed, we will add additional configuration support
 * as needed.
 *
 * The config can only be used once, by calling [consume].
 */
public class OakSessionConfigBuilder {
  public static void loadNativeLib() {
    System.loadLibrary("oak_session_config_builder_jni");
  }

  public enum AttestationType {
    BIDIRECTIONAL,
    SELF_UNIDIRECTIONAL,
    PEER_UNIDIRECTIONAL,
    UNATTESTED,
  }

  public enum HandshakeType {
    NOISE_KK,
    NOISE_KN,
    NOISE_NK,
    NOISE_NN,
  }

  private AtomicLong nativePtr;

  public OakSessionConfigBuilder(AttestationType attestationType, HandshakeType handshakeType) {
    this(nativeCreateConfigBuilder(attestationType.ordinal(), handshakeType.ordinal()));
  }

  private OakSessionConfigBuilder(long nativePtr) {
    this.nativePtr = new AtomicLong(nativePtr);
  }

  public long consume() {
    long result = this.nativePtr.getAndSet(0);
    if (result == 0) {
      throw new IllegalStateException("This config builder has already been used.");
    }
    return result;
  }

  private static native long nativeCreateConfigBuilder(int attestationType, int handshakeType);
}

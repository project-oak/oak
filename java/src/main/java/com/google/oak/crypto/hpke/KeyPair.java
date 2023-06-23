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

package com.google.oak.crypto.hpke;

import com.google.oak.util.Result;

public class KeyPair {
  static {
    try {
      System.loadLibrary("hpke-jni");
    } catch (UnsatisfiedLinkError e) {
      System.exit(1);
    }
  }

  public final byte[] privateKey;
  public final byte[] publicKey;

  private static native KeyPair nativeGenerate();

  public static final Result<KeyPair, Exception> Generate() {
    KeyPair kp = nativeGenerate();
    if (kp == null) {
      return Result.error(new Exception("Failed to generate KeyPair."));
    }
    return Result.success(kp);
  }

  private KeyPair(byte[] privateKey, byte[] publicKey) {
    this.privateKey = privateKey;
    this.publicKey = publicKey;
  }
}

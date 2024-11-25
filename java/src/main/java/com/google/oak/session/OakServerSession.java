//
// Copyright 2022 The Project Oak Authors
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

import com.google.oak.session.v1.PlaintextMessage;
import com.google.oak.session.v1.SessionRequest;
import com.google.oak.session.v1.SessionResponse;
import com.google.protobuf.ExtensionRegistry;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.Optional;

/** Class representing a streaming Oak Session using the Noise protocol (server). */
public class OakServerSession implements AutoCloseable {
  // Managed by the native code.
  private final long nativePtr;

  private OakServerSession(long nativePtr) {
    this.nativePtr = nativePtr;
  }

  public static void loadNativeLib() {
    System.loadLibrary("oak_server_session_jni");
  }

  /** Returns true if the message was expected, false otherwise. */
  public boolean putIncomingMessage(SessionRequest request) {
    return nativePutIncomingMessage(nativePtr, request.toByteArray());
  }

  public Optional<SessionResponse> getOutgoingMessage() {
    byte[] serializedMessage = nativeGetOutgoingMessage(nativePtr);
    if (serializedMessage == null) {
      return Optional.empty();
    }
    try {
      return Optional.of(
          SessionResponse.parseFrom(serializedMessage, ExtensionRegistry.getEmptyRegistry()));
    } catch (InvalidProtocolBufferException e) {
      throw new OakSessionException("Couldn't parse the proto from the native session", e);
    }
  }

  public boolean isOpen() {
    return nativeIsSessionOpen(nativePtr);
  }

  public Optional<PlaintextMessage> read() {
    byte[] serializedMessage = nativeRead(nativePtr);
    if (serializedMessage == null) {
      return Optional.empty();
    }
    try {
      return Optional.of(
          PlaintextMessage.parseFrom(serializedMessage, ExtensionRegistry.getEmptyRegistry()));
    } catch (InvalidProtocolBufferException e) {
      throw new OakSessionException("Couldn't parse the proto from the native session", e);
    }
  }

  public void write(PlaintextMessage plaintext) {
    nativeWrite(nativePtr, plaintext.toByteArray());
  }

  /**
   * Closes the underlying native session. Must be called in order to avoid a dangerous dangling
   * pointer since while the session is open the corresponding session key is also kept in memory.
   */
  @Override
  public void close() {
    nativeClose(nativePtr);
  }

  private static native long nativeCreateServerSessionUnattested();

  private static native boolean nativePutIncomingMessage(long nativePtr, byte[] request);

  private static native byte[] nativeGetOutgoingMessage(long nativePtr);

  private static native boolean nativeIsSessionOpen(long nativePtr);

  private static native byte[] nativeRead(long nativePtr);

  private static native void nativeWrite(long nativePtr, byte[] plaintext);

  private static native void nativeClose(long nativePtr);

  public static OakServerSession createServerUnattested() {
    long nativePtr = nativeCreateServerSessionUnattested();
    return new OakServerSession(nativePtr);
  }
}

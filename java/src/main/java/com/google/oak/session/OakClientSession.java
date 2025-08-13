//
// Copyright 2024 The Project Oak Authors
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

import com.google.oak.session.OakSessionConfigBuilder.AttestationType;
import com.google.oak.session.OakSessionConfigBuilder.HandshakeType;
import com.google.oak.session.v1.PlaintextMessage;
import com.google.oak.session.v1.SessionRequest;
import com.google.oak.session.v1.SessionResponse;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.Optional;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Class representing a streaming Oak Session using the Noise protocol (client).
 */
public class OakClientSession implements AutoCloseable {
  private final Lock nativeCallLock = new ReentrantLock();
  private final long nativePtr;
  private boolean closed = false;

  public OakClientSession(OakSessionConfigBuilder builder) {
    nativeCallLock.lock();
    try {
      this.nativePtr = nativeCreateClientSession(builder.consume());
    } finally {
      nativeCallLock.unlock();
    }
  }

  public static void loadNativeLib() {
    System.loadLibrary("oak_client_session_jni");
  }

  /** Returns true if the message was expected, false otherwise. */
  public boolean putIncomingMessage(SessionResponse response) {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      return nativePutIncomingMessage(nativePtr, response.toByteArray());
    } finally {
      nativeCallLock.unlock();
    }
  }

  public Optional<SessionRequest> getOutgoingMessage() {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      byte[] serializedMessage = nativeGetOutgoingMessage(nativePtr);
      if (serializedMessage == null) {
        return Optional.empty();
      }
      try {
        return Optional.of(SessionRequest.parseFrom(serializedMessage));
      } catch (InvalidProtocolBufferException e) {
        throw new OakSessionException("Couldn't parse the proto from the native session", e);
      }
    } finally {
      nativeCallLock.unlock();
    }
  }

  public boolean isOpen() {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      return nativeIsSessionOpen(nativePtr);
    } finally {
      nativeCallLock.unlock();
    }
  }

  public Optional<PlaintextMessage> read() {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      byte[] serializedMessage = nativeRead(nativePtr);
      if (serializedMessage == null) {
        return Optional.empty();
      }
      try {
        return Optional.of(PlaintextMessage.parseFrom(serializedMessage));
      } catch (InvalidProtocolBufferException e) {
        throw new OakSessionException("Couldn't parse the proto from the native session", e);
      }
    } finally {
      nativeCallLock.unlock();
    }
  }

  public void write(PlaintextMessage plaintext) {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      nativeWrite(nativePtr, plaintext.toByteArray());
    } finally {
      nativeCallLock.unlock();
    }
  }

  public byte[] getSessionBindingToken(byte[] info) {
    nativeCallLock.lock();
    try {
      if (closed) {
        throw new IllegalStateException("Session was closed");
      }
      return nativeGetSessionBindingToken(nativePtr, info);
    } finally {
      nativeCallLock.unlock();
    }
  }

  /**
   * Closes the underlying native session. Must be called in order to avoid a
   * dangerous dangling pointer since while the session is open the corresponding
   * session key is also kept in memory.
   */
  @Override
  public void close() {
    nativeCallLock.lock();
    try {
      if (closed) {
        return;
      }
      nativeClose(nativePtr);
      closed = true;
    } finally {
      nativeCallLock.unlock();
    }
  }

  // Native method declarations.
  private static native long nativeCreateClientSession(long nativeBuilderPtr);

  private static native boolean nativePutIncomingMessage(long nativePtr, byte[] request);

  private static native byte[] nativeGetOutgoingMessage(long nativePtr);

  private static native boolean nativeIsSessionOpen(long nativePtr);

  private static native byte[] nativeRead(long nativePtr);

  private static native void nativeWrite(long nativePtr, byte[] plaintext);

  private static native byte[] nativeGetSessionBindingToken(long nativePtr, byte[] info);

  private static native void nativeClose(long nativePtr);
}

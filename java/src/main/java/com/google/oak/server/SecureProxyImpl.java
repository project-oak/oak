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

package com.google.oak.server;

import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.server.ConnectionAdapter;
import com.google.oak.server.EncryptedStreamObserver;
import com.google.oak.server.SecureProxyGrpc.SecureProxyImplBase;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.util.Result;
import io.grpc.stub.ServerCallStreamObserver;
import io.grpc.stub.StreamObserver;

/**
 * The implementation of a secure proxy for wrapping an unencrypted bidirectional gRPC streaming
 * method in an encrypted connection.
 *
 * @param <I> Type of the requests in the unencrypted gRPC streaming method
 * @param <O> Type of the responses in the unencrypted gRPC streaming method
 */
public final class SecureProxyImpl<I, O> extends SecureProxyImplBase {
  private final KeyPair keyPair;
  private final ConnectionAdapter<I, O> connectionAdapter;

  /**
   * Create and return an instance of {@code SecureProxyImpl}, for adding encryption, using the
   * given {@code keyPair}, to the unencrypted bidirectional streaming gRPC method given in {@code
   * connectionAdapter}.
   * @param <I> Type of the requests in the unencrypted gRPC streaming method
   * @param <O> Type of the responses in the unencrypted gRPC streaming method
   * @param keyPair The server's key pair used for encryption
   * @param connectionAdapter Adapter for interaction with the unencrypted bidirectional streaming
   *     gRPC method
   * @return and instance of SecureProxyImpl
   */
  public static <I, O> SecureProxyImpl<I, O> create(
      KeyPair keyPair, ConnectionAdapter<I, O> connectionAdapter) {
    return new SecureProxyImpl<>(connectionAdapter, keyPair);
  }

  /**
   * Tries to create and return an instance of {@code SecureProxyImpl}, for adding encryption, by
   * generating a {@code KeyPair}, to the unencrypted bidirectional streaming gRPC method given in
   * {@code connectionAdapter}. Returns an error if generating the {@code KeyPair} fails.
   * @param <I> Type of the requests in the unencrypted gRPC streaming method
   * @param <O> Type of the responses in the unencrypted gRPC streaming method
   * @param connectionAdapter Adapter for interaction with the unencrypted bidirectional streaming
   *     gRPC method
   * @return and instance of {@code SecureProxyImpl} wrapped in a {@code Result}, or an error
   */
  public static <I, O> Result<SecureProxyImpl<I, O>, Exception> create(
      ConnectionAdapter<I, O> connectionAdapter) {
    // TODO(#3640): Perform an attestation of the key.
    return KeyPair.generate().map(keyPair -> new SecureProxyImpl<>(connectionAdapter, keyPair));
  }

  private SecureProxyImpl(ConnectionAdapter<I, O> connectionAdapter, KeyPair keyPair) {
    this.keyPair = keyPair;
    this.connectionAdapter = connectionAdapter;
  }

  @Override
  public StreamObserver<RequestWrapper> encryptedConnect(
      final StreamObserver<ResponseWrapper> outboundObserver) {
    ServerCallStreamObserver<ResponseWrapper> serverStreamObserver =
        (ServerCallStreamObserver<ResponseWrapper>) outboundObserver;
    return EncryptedStreamObserver.create(
        this.keyPair, this.connectionAdapter, serverStreamObserver);
  }
}

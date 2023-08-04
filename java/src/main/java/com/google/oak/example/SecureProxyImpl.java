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

package com.google.oak.example;

import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.example.encrypted.SecureProxyGrpc.SecureProxyImplBase;
import com.google.oak.server.ConnectionAdapter;
import com.google.oak.server.EncryptedStreamObserver;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.util.Result;
import io.grpc.stub.ServerCallStreamObserver;
import io.grpc.stub.StreamObserver;

/** */
final class SecureProxyImpl<I, O> extends SecureProxyImplBase {
  private final KeyPair keyPair;
  private final ConnectionAdapter<I, O> connectionAdapter;

  public static <I, O> Result<SecureProxyImpl<I, O>, Exception> create(
      ConnectionAdapter<I, O> connectionAdapter) {
    return KeyPair.generate().map(keyPair -> new SecureProxyImpl<>(connectionAdapter, keyPair));
  }

  public SecureProxyImpl(ConnectionAdapter<I, O> connectionAdapter, KeyPair keyPair) {
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

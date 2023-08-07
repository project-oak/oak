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
import com.google.oak.example.encrypted.Request;
import com.google.oak.example.encrypted.Response;
import com.google.oak.example.encrypted.SecureServiceGrpc.SecureServiceImplBase;
import com.google.oak.server.ConnectionAdapter;
import com.google.oak.server.EncryptedStreamObserver;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.util.Result;
import io.grpc.stub.ServerCallStreamObserver;
import io.grpc.stub.StreamObserver;
import java.util.logging.Level;
import java.util.logging.Logger;

final class SecureServiceImpl extends SecureServiceImplBase {
  private static final Logger logger = Logger.getLogger(SecureServiceImpl.class.getName());

  final KeyPair keyPair;

  public static Result<SecureServiceImpl, Exception> create() {
    return KeyPair.generate().map(SecureServiceImpl::new);
  }

  private SecureServiceImpl(KeyPair keyPair) {
    this.keyPair = keyPair;
  }

  @Override
  public StreamObserver<Request> connect(final StreamObserver<Response> outboundObserver) {
    return new StreamObserver<Request>() {
      @Override
      public void onNext(Request message) {
        logger.log(Level.INFO, "Received message");
        // Echo the message, without any further processing.
        outboundObserver.onNext(Response.newBuilder().setData(message.getData()).build());
      }

      @Override
      public void onError(Throwable error) {
        outboundObserver.onError(error);
      }

      @Override
      public void onCompleted() {
        outboundObserver.onCompleted();
      }
    };
  }

  @Override
  public StreamObserver<RequestWrapper> encryptedConnect(
      final StreamObserver<ResponseWrapper> outboundObserver) {
    ServerCallStreamObserver<ResponseWrapper> serverStreamObserver =
        (ServerCallStreamObserver<ResponseWrapper>) outboundObserver;
    return EncryptedStreamObserver.create(this.keyPair,
        new ConnectionAdapter<>(Request::parseFrom, Response::toByteArray, this::connect),
        serverStreamObserver);
  }
}

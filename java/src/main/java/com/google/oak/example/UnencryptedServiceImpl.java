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

import com.google.oak.example.encrypted.Request;
import com.google.oak.example.encrypted.Response;
import com.google.oak.example.encrypted.UnencryptedServiceGrpc.UnencryptedServiceImplBase;
import io.grpc.stub.StreamObserver;
import java.util.logging.Level;
import java.util.logging.Logger;

public final class UnencryptedServiceImpl extends UnencryptedServiceImplBase {
  private static final Logger logger = Logger.getLogger(UnencryptedServiceImpl.class.getName());

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
}

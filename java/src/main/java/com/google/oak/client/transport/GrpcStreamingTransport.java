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

package com.google.oak.client.transport;

import static java.util.concurrent.TimeUnit.SECONDS;

import com.google.oak.client.transport.EvidenceProvider;
import com.google.oak.client.transport.Transport;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import io.grpc.ManagedChannel;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.session.noninteractive.v1.AttestationBundle;
import oak.session.noninteractive.v1.GetPublicKeyRequest;
import oak.session.noninteractive.v1.GetPublicKeyResponse;
import oak.session.noninteractive.v1.InvokeRequest;
import oak.session.noninteractive.v1.InvokeResponse;
import oak.session.noninteractive.v1.RequestWrapper;
import oak.session.noninteractive.v1.ResponseWrapper;

public class GrpcStreamingTransport implements EvidenceProvider, Transport {
  private static final Logger logger = Logger.getLogger(GrpcStreamingTransport.class.getName());

  private BlockingQueue<ResponseWrapper> messageQueue;
  private StreamObserver<RequestWrapper> requestObserver;

  /**
   * Creates an instance of {@code GrpcStreamingTransport}.
   *
   * @param stream a method reference to a gRPC client streaming method with the appropriate request
   * and response types.
   */
  public GrpcStreamingTransport(
      Function<StreamObserver<ResponseWrapper>, StreamObserver<RequestWrapper>> stream) {
    // We expect to receive a single response message for each request.
    this.messageQueue = new ArrayBlockingQueue<>(1);
    StreamObserver<ResponseWrapper> responseObserver = new StreamObserver<ResponseWrapper>() {
      @Override
      public void onNext(ResponseWrapper response) {
        try {
          logger.log(Level.INFO, "messageQueue.put(", response);
          messageQueue.put(response);
        } catch (Exception e) {
          if (e instanceof InterruptedException) {
            Thread.currentThread().interrupt();
          }
          logger.log(Level.WARNING, "Couldn't send server response to the message queue: " + e);
        }
      }

      @Override
      public void onError(Throwable t) {
        Status status = Status.fromThrowable(t);
        logger.log(Level.WARNING, "Couldn't receive response: " + status);
      }

      @Override
      public void onCompleted() {
        logger.log(Level.FINE, "response message queue completed");
      }
    };
    this.requestObserver = stream.apply(responseObserver);
  }

  /**
   * Returns evidence about the trustworthiness of a remote server.
   *
   * @return {@code AttestationBundle} wrapped in a {@code Result}
   */
  public Result<AttestationBundle, Exception> getEvidence() {
    try {
      RequestWrapper requestWrapper = RequestWrapper.newBuilder()
                                          .setGetPublicKeyRequest(GetPublicKeyRequest.newBuilder())
                                          .build();
      logger.log(Level.INFO, "sending get evidence request: " + requestWrapper);
      this.requestObserver.onNext(requestWrapper);

      ResponseWrapper responseWrapper = this.messageQueue.poll(10, SECONDS);
      logger.log(Level.INFO, "received get evidence response: " + responseWrapper);
      GetPublicKeyResponse response = responseWrapper.getGetPublicKeyResponse();

      return Result.success(response.getAttestationBundle());
    } catch (InterruptedException e) {
      return Result.error(e);
    }
  }

  /**
   * Sends a request to the enclave and returns a response.
   *
   * @param requestBytes a serialized {@code oak.crypto.EncryptedRequest} wrapped in a {@code
   *     Result}
   * @return a serialized {@code oak.crypto.EncryptedResponse} wrapped in a {@code Result}
   */
  public Result<byte[], Exception> invoke(byte[] requestBytes) {
    try {
      RequestWrapper requestWrapper =
          RequestWrapper.newBuilder()
              .setInvokeRequest(
                  InvokeRequest.newBuilder().setEncryptedBody(ByteString.copyFrom(requestBytes)))
              .build();
      logger.log(Level.INFO, "sending invoke request: " + requestWrapper);
      this.requestObserver.onNext(requestWrapper);

      ResponseWrapper responseWrapper = this.messageQueue.poll(10, SECONDS);
      logger.log(Level.INFO, "received invoke response: " + responseWrapper);
      InvokeResponse response = responseWrapper.getInvokeResponse();

      return Result.success(response.getEncryptedBody().toByteArray());
    } catch (InterruptedException e) {
      return Result.error(e);
    }
  }
}

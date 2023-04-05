//
// Copyright 2021 The Project Oak Authors
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

package com.google.oak.client;

import static java.nio.charset.StandardCharsets.UTF_8;
import static java.util.concurrent.TimeUnit.SECONDS;

import com.google.protobuf.ByteString;
import com.google.protobuf.InvalidProtocolBufferException;
import io.grpc.ManagedChannel;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.nio.ByteBuffer;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.crypto.AeadEncryptedMessage;
import oak.crypto.EncryptedRequest;
import oak.crypto.EncryptedResponse;
import oak.session.noninteractive.v1.InvokeRequest;
import oak.session.noninteractive.v1.InvokeResponse;
import oak.session.noninteractive.v1.RequestWrapper;
import oak.session.noninteractive.v1.ResponseWrapper;

/** Client with remote attestation support for sending requests to an Oak application over gRPC. */
public class OakGrpcClient {
  private static final Logger logger = Logger.getLogger(OakGrpcClient.class.getName());

  // Invoke the provided method by fetching and verifying the attested enclave public key, and then
  // using it to encrypt the request body.
  //
  // The `stream` argument must be a method reference to a gRPC client streaming method with the
  // appropriate request and response types.
  //
  // TODO(#3466): Actually implement attestation and encryption.
  public static byte[] invoke(
      Function<StreamObserver<ResponseWrapper>, StreamObserver<RequestWrapper>> stream,
      byte[] requestBody) throws InterruptedException, InvalidProtocolBufferException {
    // We expect to receive a single response message.
    BlockingQueue<ResponseWrapper> messageQueue = new ArrayBlockingQueue<>(1);
    StreamObserver<ResponseWrapper> responseObserver = new StreamObserver<ResponseWrapper>() {
      @Override
      public void onNext(ResponseWrapper response) {
        try {
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
    StreamObserver<RequestWrapper> requestObserver = stream.apply(responseObserver);

    // TODO(#3642): Use HPKE to encrypt/decrypt messages.
    EncryptedRequest encryptedRequest =
        EncryptedRequest.newBuilder()
            .setSerializedEncapsulatedPublicKey(ByteString.EMPTY)
            .setEncryptedMessage(AeadEncryptedMessage.newBuilder()
                                     .setCiphertext(ByteString.copyFrom(requestBody))
                                     .setAssociatedData(ByteString.EMPTY))
            .build();

    RequestWrapper requestWrapper =
        RequestWrapper.newBuilder()
            .setInvokeRequest(InvokeRequest.newBuilder().setEncryptedBody(
                ByteString.copyFrom(encryptedRequest.toByteArray())))
            .build();
    logger.log(Level.INFO, "request wrapper: " + requestWrapper);
    requestObserver.onNext(requestWrapper);

    ResponseWrapper responseWrapper = messageQueue.poll(10, SECONDS);
    logger.log(Level.INFO, "response wrapper: " + responseWrapper);
    InvokeResponse response = responseWrapper.getInvokeResponse();

    byte[] responseBody = EncryptedResponse.parseFrom(response.getEncryptedBody().toByteArray())
                              .getEncryptedMessage()
                              .getCiphertext()
                              .toByteArray();
    return responseBody;
  }
}

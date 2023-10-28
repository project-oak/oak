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

package com.google.oak.transport;

import com.google.oak.session.v1.EndorsedEvidence;
import com.google.oak.session.v1.GetEndorsedEvidenceRequest;
import com.google.oak.session.v1.GetEndorsedEvidenceResponse;
import com.google.oak.session.v1.InvokeRequest;
import com.google.oak.session.v1.InvokeResponse;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import io.grpc.stub.StreamObserver;
import java.time.Duration;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.logging.Logger;

public class GrpcStreamingTransport implements EvidenceProvider, Transport {
  private static final Logger logger = Logger.getLogger(GrpcStreamingTransport.class.getName());

  private static final Duration TIMEOUT = Duration.ofSeconds(10);

  /**
   * QueueingStreamObserver with a queue containing responses received from the
   * server.
   * The queue size is 1 because we expect to receive a single response message
   * for each request.
   */
  QueueingStreamObserver<ResponseWrapper> responseObserver = new QueueingStreamObserver<>(1);
  private final StreamObserver<RequestWrapper> requestObserver;

  /**
   * Creates an instance of {@code GrpcStreamingTransport}.
   *
   * @param stream a method reference to a gRPC client streaming method with the
   *               appropriate request
   *               and response types.
   */
  public GrpcStreamingTransport(
      Function<StreamObserver<ResponseWrapper>, StreamObserver<RequestWrapper>> stream) {
    this.requestObserver = stream.apply(responseObserver);
  }

  /**
   * Returns evidence about the trustworthiness of a remote server.
   *
   * @return {@code EndorsedEvidence} wrapped in a {@code Result}
   */
  @Override
  public Result<EndorsedEvidence, String> getEvidence() {
    RequestWrapper requestWrapper = RequestWrapper.newBuilder()
                                        .setGetEndorsedEvidenceRequest(GetEndorsedEvidenceRequest.newBuilder())
                                        .build();
    logger.log(Level.INFO, "sending get public key request: " + requestWrapper);
    this.requestObserver.onNext(requestWrapper);

    ResponseWrapper responseWrapper;
    try {
      // TODO(#3644): Add retry for client messages.
      responseWrapper = this.responseObserver.poll(TIMEOUT);
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      return Result.error("Thread interrupted while waiting for a response");
    }
    if (responseWrapper == null) {
      return Result.error("No response message received");
    }

    logger.log(Level.INFO, "received get public key response: " + responseWrapper);
    GetEndorsedEvidenceResponse response = responseWrapper.getGetEndorsedEvidenceResponse();

    return Result.success(response.getEndorsedEvidence());
  }

  /**
   * Sends a request to the enclave and returns a response.
   *
   * @param requestBytes a serialized {@code oak.crypto.EncryptedRequest} wrapped
   *                     in a {@code
   *     Result}
   * @return a serialized {@code oak.crypto.EncryptedResponse} wrapped in a
   *         {@code Result}
   */
  @Override
  public Result<byte[], String> invoke(byte[] requestBytes) {
    RequestWrapper requestWrapper =
        RequestWrapper.newBuilder()
            .setInvokeRequest(
                InvokeRequest.newBuilder().setEncryptedBody(ByteString.copyFrom(requestBytes)))
            .build();
    logger.log(Level.INFO, "sending invoke request: " + requestWrapper);
    this.requestObserver.onNext(requestWrapper);

    ResponseWrapper responseWrapper;
    try {
      // TODO(#3644): Add retry for client messages.
      responseWrapper = this.responseObserver.poll(TIMEOUT);
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      return Result.error("Thread interrupted while waiting for a response");
    }
    if (responseWrapper == null) {
      return Result.error("No response message received");
    }

    logger.log(Level.INFO, "received invoke response: " + responseWrapper);
    InvokeResponse response = responseWrapper.getInvokeResponse();

    return Result.success(response.getEncryptedBody().toByteArray());
  }

  @Override
  public void close() throws Exception {
    this.requestObserver.onCompleted();
  }
}

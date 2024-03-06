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

import static org.mockito.AdditionalAnswers.delegatesTo;
import static org.mockito.Mockito.mock;

import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.session.v1.EndorsedEvidence;
import com.google.oak.session.v1.GetEndorsedEvidenceResponse;
import com.google.oak.session.v1.InvokeResponse;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.session.v1.StreamingSessionGrpc;
import com.google.oak.transport.GrpcStreamingTransport;
import com.google.oak.util.Result;
import io.grpc.ManagedChannel;
import io.grpc.inprocess.InProcessChannelBuilder;
import io.grpc.inprocess.InProcessServerBuilder;
import io.grpc.stub.StreamObserver;
import io.grpc.testing.GrpcCleanupRule;
import java.lang.IllegalArgumentException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class GrpcStreamingTransportTest {
  private static class RequestStreamObserver implements StreamObserver<RequestWrapper> {
    private final StreamObserver<ResponseWrapper> responseObserver;

    RequestStreamObserver(StreamObserver<ResponseWrapper> responseObserver) {
      this.responseObserver = responseObserver;
    }

    @Override
    public void onNext(RequestWrapper request) {
      ResponseWrapper responseWrapper;
      RequestWrapper.RequestCase requestCase = request.getRequestCase();
      switch (requestCase) {
        case GET_ENDORSED_EVIDENCE_REQUEST:
          responseWrapper = ResponseWrapper.newBuilder()
                                .setGetEndorsedEvidenceResponse(
                                    GetEndorsedEvidenceResponse.newBuilder().setEndorsedEvidence(
                                        EndorsedEvidence.newBuilder()
                                            .setEvidence(Evidence.getDefaultInstance())
                                            .setEndorsements(Endorsements.getDefaultInstance())))
                                .build();
          responseObserver.onNext(responseWrapper);
          break;
        case INVOKE_REQUEST:
          responseWrapper = ResponseWrapper.newBuilder()
                                .setInvokeResponse(InvokeResponse.newBuilder().setEncryptedResponse(
                                    EncryptedResponse.getDefaultInstance()))
                                .build();
          responseObserver.onNext(responseWrapper);
          break;
        case REQUEST_NOT_SET:
          responseObserver.onError(new IllegalArgumentException());
          break;
      }
    }

    @Override
    public void onError(Throwable t) {
      responseObserver.onError(t);
    }

    @Override
    public void onCompleted() {
      responseObserver.onCompleted();
    }
  }

  private final StreamingSessionGrpc.StreamingSessionImplBase serviceImpl =
      mock(StreamingSessionGrpc.StreamingSessionImplBase.class,
          delegatesTo(new StreamingSessionGrpc.StreamingSessionImplBase() {
            @Override
            public StreamObserver<RequestWrapper> stream(
                StreamObserver<ResponseWrapper> responseObserver) {
              return new RequestStreamObserver(responseObserver);
            }
          }));

  /**
   * This rule manages automatic graceful shutdown for the registered servers and
   * channels at the end of test.
   */
  @Rule public final GrpcCleanupRule grpcCleanup = new GrpcCleanupRule();

  private StreamingSessionGrpc.StreamingSessionStub client;

  @Before
  public void setUp() throws Exception {
    // Generate a unique in-process server name.
    String serverName = InProcessServerBuilder.generateName();

    // Create a server, add service, start, and register for automatic graceful
    // shutdown.
    grpcCleanup.register(InProcessServerBuilder.forName(serverName)
                             .directExecutor()
                             .addService(serviceImpl)
                             .build()
                             .start());

    // Create a client channel and register for automatic graceful shutdown.
    ManagedChannel channel =
        grpcCleanup.register(InProcessChannelBuilder.forName(serverName).directExecutor().build());

    // Create a client using the in-process channel;
    client = StreamingSessionGrpc.newStub(channel);
  }

  @Test
  public void testGrpcStreamingTransport() throws Exception {
    GrpcStreamingTransport transport = new GrpcStreamingTransport(client::stream);

    Result<EndorsedEvidence, String> getEndorsedEvidenceResult = transport.getEndorsedEvidence();
    Assert.assertTrue(getEndorsedEvidenceResult.isSuccess());

    Result<EncryptedResponse, String> invokeResult =
        transport.invoke(EncryptedRequest.getDefaultInstance());
    Assert.assertTrue(invokeResult.isSuccess());
    Assert.assertEquals(
        invokeResult.unwrap("missing result"), EncryptedResponse.getDefaultInstance());

    // The following call may throw a general {@code Exception}.
    // The test succeeds if it doesn't throw an exception.
    transport.close();
  }
}

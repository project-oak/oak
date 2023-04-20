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

import com.google.oak.transport.GrpcStreamingTransport;
import com.google.oak.util.Result;
import io.grpc.ManagedChannel;
import io.grpc.stub.StreamObserver;
import io.grpc.testing.GrpcCleanupRule;
import io.grpc.inprocess.InProcessChannelBuilder;
import io.grpc.inprocess.InProcessServerBuilder;
import java.nio.charset.StandardCharsets;
import java.util.function.Function;
import java.util.Optional;
import oak.session.noninteractive.v1.RequestWrapper;
import oak.session.noninteractive.v1.ResponseWrapper;
import oak.session.noninteractive.v1.StreamingSessionGrpc;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.Rule;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.Mockito;

@RunWith(JUnit4.class)
public class GrpcStreamingTransportTest {
  @Rule
  public final GrpcCleanupRule grpcCleanup = new GrpcCleanupRule();

  private final StreamingSessionGrpc.StreamingSessionImplBase serviceImpl =
      mock(StreamingSessionGrpc.StreamingSessionImplBase.class, delegatesTo(
          new StreamingSessionGrpc.StreamingSessionImplBase() {
            @Override
            public StreamObserver<RequestWrapper> stream(StreamObserver<ResponseWrapper> responseObserver) {
              StreamObserver<RequestWrapper> requestObserver = new StreamObserver<RequestWrapper>() {
                @Override
                public void onNext(RequestWrapper request) {
                  responseObserver.onNext(ResponseWrapper.getDefaultInstance());
                }

                @Override
                public void onError(Throwable t) {}

                @Override
                public void onCompleted() {
                  responseObserver.onCompleted();
                }
              };
              return requestObserver;
            }
          }));

  private StreamingSessionGrpc.StreamingSessionStub client;

  @Before
  public void setUp() throws Exception {
    // Generate a unique in-process server name.
    String serverName = InProcessServerBuilder.generateName();

    // Create a server, add service, start, and register for automatic graceful shutdown.
    grpcCleanup.register(InProcessServerBuilder
        .forName(serverName).directExecutor().addService(serviceImpl).build().start());

    // Create a client channel and register for automatic graceful shutdown.
    ManagedChannel channel = grpcCleanup.register(
        InProcessChannelBuilder.forName(serverName).directExecutor().build());

    // Create a client using the in-process channel;
    StreamingSessionGrpc.StreamingSessionStub client = StreamingSessionGrpc.newStub(channel);
  }

  @Test
  public void testGetEvidence() throws Exception {
    // TODO(#3644): Implement a unit test for gRPC streaming.
    Assert.assertNotNull(client);
    GrpcStreamingTransport transport = new GrpcStreamingTransport(client::stream);

    // Function<StreamObserver<ResponseWrapper>, StreamObserver<RequestWrapper>> stream =
    //     client::stream;

    // StreamObserver<ResponseWrapper> responseObserver = new StreamObserver<ResponseWrapper>() {
    //   @Override
    //   public void onNext(ResponseWrapper response) {}

    //   @Override
    //   public void onError(Throwable t) {}

    //   @Override
    //   public void onCompleted() {}
    // };
    // StreamObserver<RequestWrapper> requestObserver = client.stream(responseObserver);
  }
}

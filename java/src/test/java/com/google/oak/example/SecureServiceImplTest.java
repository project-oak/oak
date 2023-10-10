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

import static java.util.concurrent.TimeUnit.SECONDS;
import static junit.framework.Assert.assertEquals;
import static junit.framework.Assert.assertTrue;

import com.google.oak.client.OakClient;
import com.google.oak.example.encrypted.Request;
import com.google.oak.example.encrypted.Response;
import com.google.oak.example.encrypted.SecureServiceGrpc;
import com.google.oak.remote_attestation.InsecureAttestationVerifier;
import com.google.oak.transport.GrpcStreamingTransport;
import com.google.protobuf.ByteString;
import com.google.protobuf.ExtensionRegistryLite;
import io.grpc.ManagedChannel;
import io.grpc.Server;
import io.grpc.inprocess.InProcessChannelBuilder;
import io.grpc.inprocess.InProcessServerBuilder;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public final class SecureServiceImplTest {
  private Server server;
  private ManagedChannel channel;

  @Before
  public void setUp() throws Exception {
    String serverName = InProcessServerBuilder.generateName();
    server = InProcessServerBuilder.forName(serverName)
                 .directExecutor()
                 .addService(SecureServiceImpl.create().unwrap("creating service"))
                 .build()
                 .start();
    channel = InProcessChannelBuilder.forName(serverName).directExecutor().build();
  }

  @After
  public void tearDown() throws Exception {
    assertTrue(server.shutdown().awaitTermination(5, SECONDS));
    assertTrue(channel.shutdown().awaitTermination(5, SECONDS));
  }

  @Test
  public void encryptedConnectTest_singleMessage() throws Exception {
    String message = "Hello World!";
    SecureServiceGrpc.SecureServiceStub stub = SecureServiceGrpc.newStub(channel);
    GrpcStreamingTransport transport = new GrpcStreamingTransport(stub::encryptedConnect);

    try (OakClient<GrpcStreamingTransport> oakClient =
             OakClient.create(transport, new InsecureAttestationVerifier())
                 .unwrap("creating client")) {
      Request request = Request.newBuilder().setData(ByteString.copyFromUtf8(message)).build();
      byte[] bytes = oakClient.invoke(request.toByteArray()).unwrap("invoking client");
      Response response = Response.parseFrom(bytes, ExtensionRegistryLite.getEmptyRegistry());

      assertEquals(response.getData().toStringUtf8(), message);
    }
  }
}

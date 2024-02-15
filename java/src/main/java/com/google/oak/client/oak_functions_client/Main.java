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

package com.google.oak.client.oak_functions_client;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.micro_rpc.ResponseWrapper;
import com.google.oak.client.OakClient;
import com.google.oak.remote_attestation.InsecureAttestationVerifier;
import com.google.oak.session.v1.StreamingSessionGrpc;
import com.google.oak.transport.ApiKeyInterceptor;
import com.google.oak.transport.GrpcStreamingTransport;
import com.google.oak.util.Result;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.time.Clock;
import java.util.Arrays;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
  private static Logger logger = Logger.getLogger(Main.class.getName());
  private static final String EMPTY_API_KEY = "";

  public static void main(String[] args) throws Exception {
    // Create a gRPC channel.
    URL parsedUrl = new URL(args[0]);
    ManagedChannelBuilder builder =
        ManagedChannelBuilder.forAddress(parsedUrl.getHost(), parsedUrl.getPort()).usePlaintext();
    builder.intercept(new ApiKeyInterceptor(EMPTY_API_KEY));
    ManagedChannel channel = builder.build();

    // Create gRPC client stub.
    StreamingSessionGrpc.StreamingSessionStub client = StreamingSessionGrpc.newStub(channel);

    // Create Oak Client.
    GrpcStreamingTransport transport = new GrpcStreamingTransport(client::stream);
    Result<OakClient<GrpcStreamingTransport>, Exception> oakClientCreateResult =
        OakClient.create(transport, new InsecureAttestationVerifier(), Clock.systemUTC());
    OakClient<GrpcStreamingTransport> oakClient = oakClientCreateResult.unwrap("creating client");

    byte[] requestBody = "test data".getBytes(UTF_8);
    Result<byte[], Exception> oakClientInvokeResult = oakClient.invoke(requestBody);
    byte[] responseWrapperBytes = oakClientInvokeResult.unwrap("invoking client");
    ResponseWrapper responseWrapper = ResponseWrapper.parseFrom(responseWrapperBytes);
    logger.log(Level.INFO, "Client received response wrapper: " + responseWrapper.toString());
    byte[] responseBody = responseWrapper.getBody().toByteArray();

    if (Arrays.equals(responseBody, requestBody)) {
      logger.log(
          Level.INFO, "Client received the expected response: " + Arrays.toString(responseBody));
    } else {
      logger.log(Level.INFO,
          String.format("Expected response %s, received %s.", Arrays.toString(requestBody),
              Arrays.toString(responseBody)));
      System.exit(1);
    }
  }
}

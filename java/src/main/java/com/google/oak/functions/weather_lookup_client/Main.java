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

package com.google.oak.functions.weather_lookup_client;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.oak.client.OakClient;
import com.google.oak.remote_attestation.InsecureAttestationVerifier;
import com.google.oak.transport.ApiKeyInterceptor;
import com.google.oak.transport.GrpcStreamingTransport;
import com.google.oak.util.Result;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.session.noninteractive.v1.StreamingSessionGrpc;

public class Main {
  private static Logger logger = Logger.getLogger(Main.class.getName());
  private static final String EMPTY_API_KEY = "";
  private static final String EXPECTED_RESPONSE_PATTERN =
      "\\{\"temperature_degrees_celsius\":.*\\}";

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
        OakClient.Create(transport, new InsecureAttestationVerifier());
    if (oakClientCreateResult.isError()) {
      throw oakClientCreateResult.error().get();
    }
    OakClient<GrpcStreamingTransport> oakClient = oakClientCreateResult.success().get();

    // Test request coordinates are defined in `oak_functions/lookup_data_generator/src/data.rs`.
    byte[] requestBody = "{\"lat\":0,\"lng\":0}".getBytes(UTF_8);
    Result<byte[], Exception> oakClientInvokeResult = oakClient.invoke(requestBody);
    if (oakClientInvokeResult.isError()) {
      throw oakClientInvokeResult.error().get();
    }
    byte[] response = oakClientInvokeResult.success().get();
    String decodedResponse = new String(response, StandardCharsets.UTF_8);

    if (decodedResponse.matches(EXPECTED_RESPONSE_PATTERN)) {
      logger.log(Level.INFO, "Client received the expected response: " + decodedResponse);
    } else {
      logger.log(Level.INFO,
          String.format(
              "Expected pattern %s, received %s.", EXPECTED_RESPONSE_PATTERN, decodedResponse));
      System.exit(1);
    }
  }
}

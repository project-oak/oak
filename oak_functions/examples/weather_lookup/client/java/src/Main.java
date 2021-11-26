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

package com.google.oak.functions.examples.weather_lookup.client;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.oak.functions.client.AttestationClient;
import com.google.protobuf.ByteString;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import java.net.URL;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;

public class Main {
  private static Logger logger = Logger.getLogger(Main.class.getName());
  private static final String OAK_URL = "http://localhost:8080";
  private static final String EMPTY_API_KEY = "";
  private static final String EXPECTED_RESPONSE_PATTERN =
      "\\{\"temperature_degrees_celsius\":.*\\}";

  public static void main(String[] args) throws Exception {
    // Create a gRPC channel.
    URL parsedUrl = new URL(OAK_URL);
    ManagedChannelBuilder builder =
        ManagedChannelBuilder.forAddress(parsedUrl.getHost(), parsedUrl.getPort()).usePlaintext();
    builder = AttestationClient.addApiKey(builder, EMPTY_API_KEY);
    ManagedChannel channel = builder.build();

    // Attest a gRPC channel.
    AttestationClient client = new AttestationClient();
    client.attest(channel, (config) -> !config.getMlInference());

    // Test request coordinates are defined in `oak_functions/lookup_data_generator/src/data.rs`.
    byte[] requestBody = "{\"lat\":0,\"lng\":0}".getBytes(UTF_8);
    Request request = Request.newBuilder().setBody(ByteString.copyFrom(requestBody)).build();
    Response response = client.send(request);
    client.finalize();
    ByteString responseBody = response.getBody().substring(0, (int) response.getLength());
    String decodedResponse = responseBody.toStringUtf8();

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
